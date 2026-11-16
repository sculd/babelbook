#!/usr/bin/env python3
"""babelbook: turn an EPUB (or, best effort, a PDF) into a folder of plain HTML pages.

The goal is to read books in a web browser and lean on the browser's built-in
translation. Every output page is a real, separately loaded HTML file, which is
what browser translation handles most reliably.

    babelbook.py ~/Downloads/alice.epub              -> ~/ebooks_html/alice/
    babelbook.py book.pdf --out-root ~/somewhere
    babelbook.py a.epub b.epub --serve               -> convert, then serve ~/ebooks_html
    babelbook.py --serve                             -> just serve what is already there

Pages are cut by amount of text (default about 2000 words), only at block
boundaries, never inside a table, figure or list item, and a new page starts at
each chapter. Because a page is defined by text rather than by screen size,
changing the font size in the reader never needs re-pagination; you scroll a bit.

Output layout:
    <out-root>/index.html               library page listing every converted book
    <out-root>/reader.css, reader.js    shared reader chrome (font controls, nav, position memory)
    <out-root>/<slug>/index.html        book page: cover, table of contents, "continue reading"
    <out-root>/<slug>/p001.html ...     the pages
    <out-root>/<slug>/images/           images copied out of the book
    <out-root>/<slug>/book.json         metadata, used to build the library page

EPUB needs only lxml. PDF needs PyMuPDF (pip install pymupdf).
"""
from __future__ import annotations

import argparse
import dataclasses
import html
import html.entities
import http.server
import json
import posixpath
import re
import shutil
import sys
import time
import unicodedata
import webbrowser
import zipfile
from collections import Counter
from functools import partial
from pathlib import Path
from urllib.parse import unquote, urlsplit

from lxml import etree

DEFAULT_OUT_ROOT = Path.home() / "ebooks_html"

# Block-level tags we never split and never descend into.
ATOMIC_TAGS = {
    "p", "h1", "h2", "h3", "h4", "h5", "h6", "table", "figure", "img", "blockquote",
    "pre", "ul", "ol", "dl", "hr", "svg", "video", "audio", "address", "math",
    "details", "fieldset", "form", "iframe", "object",
}
# Wrapper tags we flatten away, emitting their block children one by one.
CONTAINER_TAGS = {"div", "section", "article", "main", "header", "footer", "aside",
                  "nav", "hgroup", "body", "center"}
HEADING_TAGS = {"h1", "h2", "h3", "h4", "h5", "h6"}
SOFT_BREAK_TAGS = {"h1", "h2"}          # a new page may start before these
MEDIA_TAGS = {"img", "svg", "video", "audio", "iframe", "object", "canvas", "math"}

NAMED_ENTITY_RE = re.compile(r"&([A-Za-z][A-Za-z0-9]*);")
XML_ENTITIES = {"amp", "lt", "gt", "quot", "apos"}
ENDS_SENTENCE_RE = re.compile(r"""[.!?:;…"”’')\]]\s*$""")


# --------------------------------------------------------------------------- model

@dataclasses.dataclass
class Block:
    el: etree._Element
    tag: str
    words: int
    soft_break: bool
    file_idx: int
    src_path: str | None = None          # path inside the EPUB zip, for link resolution
    ids: list[str] = dataclasses.field(default_factory=list)
    page: int = 0


@dataclasses.dataclass
class TocEntry:
    depth: int
    label: str
    file_idx: int | None
    frag: str | None


@dataclasses.dataclass
class Book:
    title: str
    author: str
    lang: str
    slug: str
    source: str
    blocks: list[Block]
    toc: list[TocEntry]
    cover: str | None = None             # relative path like images/cover.jpg
    spine_paths: dict[str, int] = dataclasses.field(default_factory=dict)   # zip path -> file_idx
    image_map: dict[str, str] = dataclasses.field(default_factory=dict)     # zip path -> images/name


# --------------------------------------------------------------------------- helpers

def words_in(el: etree._Element) -> int:
    return len("".join(el.itertext()).split())


def text_of(el) -> str:
    return re.sub(r"\s+", " ", "".join(el.itertext())).strip() if el is not None else ""


def slugify(s: str) -> str:
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    s = re.sub(r"[^a-zA-Z0-9]+", "-", s).strip("-").lower()
    return s or "book"


def serialize(el: etree._Element) -> str:
    s = etree.tostring(el, method="html", encoding="unicode", with_tail=False)
    if el.tag == "table":
        s = f'<div class="table-wrap">{s}</div>'
    return s


def _entity_repl(m: re.Match) -> str:
    name = m.group(1)
    if name in XML_ENTITIES:
        return m.group(0)
    cp = html.entities.name2codepoint.get(name)
    return chr(cp) if cp else m.group(0)


def parse_xml(data: bytes) -> etree._Element:
    """Parse XHTML/XML leniently: tolerate HTML named entities and minor breakage."""
    text = data.decode("utf-8", errors="replace").lstrip("﻿")
    text = re.sub(r"^\s*<\?xml[^>]*\?>", "", text, count=1)
    text = NAMED_ENTITY_RE.sub(_entity_repl, text)
    parser = etree.XMLParser(recover=True, huge_tree=True, resolve_entities=False, no_network=True)
    root = etree.fromstring(text, parser)
    if root is None:
        raise ValueError("unparseable document")
    return root


def strip_ns(root: etree._Element) -> None:
    """Drop namespaces so tags are plain HTML names; keep a few useful namespaced attrs."""
    for el in root.iter():
        if not isinstance(el.tag, str):
            continue
        if "}" in el.tag:
            el.tag = el.tag.rsplit("}", 1)[1]
        for name in list(el.attrib):
            if name.startswith("{"):
                val = el.attrib.pop(name)
                local = name.rsplit("}", 1)[1]
                if local == "href" and el.tag == "image":       # xlink:href on SVG <image>
                    el.set("href", val)
                elif local == "type" and "idpf.org" in name:    # epub:type
                    el.set("data-epub-type", val)
                elif local == "lang":
                    el.set("lang", val)
    etree.cleanup_namespaces(root)


def has_block_inside(el: etree._Element) -> bool:
    return any(isinstance(d.tag, str) and (d.tag in ATOMIC_TAGS or d.tag in CONTAINER_TAGS)
               for d in el.iterdescendants())


def meaningful(el: etree._Element) -> bool:
    if "".join(el.itertext()).strip():
        return True
    return any(isinstance(d.tag, str) and (d.tag in MEDIA_TAGS or d.tag == "hr") for d in el.iter())


def flatten(container: etree._Element, out: list[etree._Element]) -> None:
    """Emit the block-level children of a container; wrap stray inline runs in <p>."""
    run_text = container.text
    run_elems: list[etree._Element] = []

    def flush() -> None:
        nonlocal run_text, run_elems
        content = (run_text or "") + "".join("".join(e.itertext()) + (e.tail or "") for e in run_elems)
        has_media = any(isinstance(d.tag, str) and d.tag in MEDIA_TAGS for e in run_elems for d in e.iter())
        if content.strip() or has_media:
            p = etree.Element("p")
            p.text = run_text
            for e in run_elems:
                p.append(e)                      # moves e (and its tail) into p
            out.append(p)
        run_text, run_elems = None, []

    for child in list(container):
        tag = child.tag if isinstance(child.tag, str) else None
        if tag in CONTAINER_TAGS or tag in ATOMIC_TAGS:
            flush()
            tail, child.tail = child.tail, None
            if tag in CONTAINER_TAGS and has_block_inside(child):
                flatten(child, out)
            else:
                out.append(child)
            run_text = tail
        else:
            run_elems.append(child)
    flush()


def split_list(el: etree._Element, max_words: int) -> list[etree._Element]:
    """Split a huge <ol>/<ul> (endnotes!) into several lists so a page can end between items."""
    items = [c for c in el if isinstance(c.tag, str) and c.tag == "li"]
    if len(items) < 2 or words_in(el) <= max_words:
        return [el]
    try:
        n = int(el.get("start", "1"))
    except ValueError:
        n = 1
    groups: list[list[etree._Element]] = [[]]
    cur = 0
    for li in items:
        w = words_in(li)
        if groups[-1] and cur + w > max_words:
            groups.append([])
            cur = 0
        groups[-1].append(li)
        cur += w
    result = []
    for g in groups:
        new = etree.Element(el.tag, dict(el.attrib))
        if el.tag == "ol":
            new.set("start", str(n))
        for li in g:
            new.append(li)
        n += len(g)
        result.append(new)
    return result


def split_blockquote(el: etree._Element, max_words: int) -> list[etree._Element]:
    """Split a long blockquote (a letter, a long quotation) between its inner paragraphs."""
    kids = [c for c in el if isinstance(c.tag, str)]
    if len(kids) < 2 or (el.text or "").strip() or any(k.tag not in ATOMIC_TAGS and k.tag not in CONTAINER_TAGS for k in kids):
        return [el]
    groups: list[list[etree._Element]] = [[]]
    cur = 0
    for k in kids:
        w = words_in(k)
        if groups[-1] and cur + w > max_words:
            groups.append([])
            cur = 0
        groups[-1].append(k)
        cur += w
    if len(groups) < 2:
        return [el]
    result = []
    for i, g in enumerate(groups):
        new = etree.Element("blockquote", dict(el.attrib))
        if i:
            new.attrib.pop("id", None)
        for k in g:
            new.append(k)
        result.append(new)
    return result


def split_p_at_br(el: etree._Element, max_words: int) -> list[etree._Element]:
    """Split a huge <p> made of <br>-separated lines (an index, a long poem) at line breaks."""
    if not any(isinstance(c.tag, str) and c.tag == "br" for c in el):
        return [el]
    parts: list[etree._Element] = []
    cur = etree.Element("p", dict(el.attrib))
    cur.text = el.text
    cw = len((el.text or "").split())
    for child in list(el):
        if isinstance(child.tag, str) and child.tag == "br" and cw >= max_words:
            parts.append(cur)
            cur = etree.Element("p", dict(el.attrib))
            cur.attrib.pop("id", None)
            cur.text = child.tail
            cw = len((child.tail or "").split())
            continue
        cw += words_in(child) + len((child.tail or "").split())
        cur.append(child)
    parts.append(cur)
    return parts if len(parts) > 1 else [el]


def split_block(el: etree._Element, max_words: int) -> list[etree._Element]:
    """Break up blocks too big for one page where that can be done without changing meaning."""
    if words_in(el) <= max_words:
        return [el]
    if el.tag in ("ol", "ul"):
        return split_list(el, max_words)
    if el.tag == "blockquote":
        return split_blockquote(el, max_words)
    if el.tag == "p":
        return split_p_at_br(el, max_words)
    return [el]


def clean_block(el: etree._Element) -> None:
    """Drop the book's inline styling so the reader stylesheet wins; keep SVG intact."""
    for d in el.iter():
        if not isinstance(d.tag, str) or d.tag == "svg":
            continue
        if next(d.iterancestors("svg"), None) is not None:
            continue
        for attr in ("style", "srcset", "sizes", "onclick", "onload"):
            d.attrib.pop(attr, None)


def remove_keep_tail(el: etree._Element) -> None:
    parent = el.getparent()
    if parent is None:
        return
    if el.tail:
        prev = el.getprevious()
        if prev is not None:
            prev.tail = (prev.tail or "") + el.tail
        else:
            parent.text = (parent.text or "") + el.tail
    parent.remove(el)


# --------------------------------------------------------------------------- CSS-based heading inference

CSS_RULE_RE = re.compile(r"([^{}]+)\{([^{}]*)\}", re.S)
SIMPLE_CLASS_SEL_RE = re.compile(r"(?:p|div|h[1-6]|span)?\.([\w-]+)")
CHAPTER_LABEL_RE = re.compile(
    r"^\W*(?:chapter|part|book|appendix|section|volume|act|canto)?\W*"
    r"(?:[ivxlcdm]+|\d+|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|"
    r"thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|first|second|third)\W*$", re.I)
KEYWORD_SIZES = {"xx-small": .6, "x-small": .75, "small": .9, "smaller": .9, "medium": 1.0,
                 "large": 1.2, "larger": 1.2, "x-large": 1.5, "xx-large": 2.0}


def size_to_em(value: str) -> float | None:
    value = value.strip().lower()
    if value in KEYWORD_SIZES:
        return KEYWORD_SIZES[value]
    m = re.match(r"([\d.]+)\s*(em|rem|%|pt|px)?$", value)
    if not m:
        return None
    n, unit = float(m.group(1)), m.group(2) or "px"
    return {"em": n, "rem": n, "%": n / 100, "pt": n / 12, "px": n / 16}[unit]


def parse_css_classes(css: str, styles: dict[str, dict] | None = None) -> dict[str, dict]:
    """Collect font-size (in em), bold and centered flags for simple class selectors."""
    styles = {} if styles is None else styles
    css = re.sub(r"/\*.*?\*/", "", css, flags=re.S)
    for selectors, body in CSS_RULE_RE.findall(css):
        decls = {}
        for d in body.split(";"):
            if ":" in d:
                k, v = d.split(":", 1)
                decls[k.strip().lower()] = v.strip().lower()
        if not decls:
            continue
        for sel in selectors.split(","):
            m = SIMPLE_CLASS_SEL_RE.fullmatch(sel.strip())
            if not m:
                continue
            st = styles.setdefault(m.group(1), {})
            if "font-size" in decls:
                em = size_to_em(decls["font-size"])
                if em:
                    st["size"] = em
            if "font-weight" in decls:
                w = decls["font-weight"]
                st["bold"] = w in ("bold", "bolder") or (w.isdigit() and int(w) >= 600)
            if "text-align" in decls:
                st["center"] = decls["text-align"] == "center"
    return styles


def class_style(el: etree._Element, styles: dict[str, dict]) -> tuple[float, bool, bool]:
    """(font size in em, bold, centered) for an element according to its classes."""
    size, bold, center = 0.0, False, False
    for c in (el.get("class") or "").split():
        st = styles.get(c)
        if not st:
            continue
        size = max(size, st.get("size", 0.0))
        bold = bold or st.get("bold", False)
        center = center or st.get("center", False)
    return size, bold, center


def infer_headings(blocks: list[Block], styles: dict[str, dict]) -> None:
    """Books with no <h1>-<h6> (Calibre output, many publishers) mark titles only via CSS.
    Promote short paragraphs set in a clearly larger font to headings, so chapters start
    new pages, pages get labels and a table of contents can be built."""
    if not styles or any(b.tag in HEADING_TAGS for b in blocks):
        return
    by_class: Counter = Counter()
    for b in blocks:
        if b.tag == "p":
            by_class[b.el.get("class") or ""] += b.words
    dominant = by_class.most_common(1)[0][0] if by_class else ""
    body_em = max((styles.get(c, {}).get("size", 0.0) for c in dominant.split()), default=0.0) or 1.0

    pos_in_file: dict[int, int] = {}
    inferred: set[int] = set()
    for i, b in enumerate(blocks):
        n = pos_in_file.get(b.file_idx, 0)
        pos_in_file[b.file_idx] = n + 1
        if b.tag not in ("p", "div"):
            continue
        text = text_of(b.el)
        if not text or len(text.split()) > 12 or len(text) > 80:
            continue
        size, bold, center = class_style(b.el, styles)
        bold = bold or any(isinstance(d.tag, str) and d.tag in ("b", "strong") for d in b.el.iter())
        level = None
        if size >= 1.5 * body_em:
            level = "h1"
        elif size >= 1.2 * body_em:
            level = "h2"
        elif n < 3 and (bold or center) and re.search(r"[^\W\d_]", text) and not text.endswith((".", ",", ";")):
            level = "h2"
        if level:
            b.el.tag = level
            b.tag = level
            b.soft_break = True
            inferred.add(i)

    # A chapter label line ("VI", "Part Two", "Appendix III") directly followed by the
    # title line: make them one heading.
    merged: list[Block] = []
    prev_inferred = False          # whether merged[-1] is an inferred heading
    prev_src = -2                  # index in `blocks` of the last block kept or absorbed
    prev_lines = 0                 # how many lines merged[-1] already holds
    for i, b in enumerate(blocks):
        prev = merged[-1] if merged else None
        if (i in inferred and prev is not None and prev_inferred and prev_src == i - 1
                and prev.file_idx == b.file_idx and prev.tag == b.tag and prev_lines < 2
                and CHAPTER_LABEL_RE.match(text_of(prev.el))):
            br = etree.SubElement(prev.el, "br")
            br.tail = " " + text_of(b.el)          # leading space keeps the label readable
            prev_src = i
            prev_lines += 1
            if prev.el.get("id") is None and b.el.get("id") is not None:
                prev.el.set("id", b.el.get("id"))
                prev.ids.extend(b.ids)
            prev.words += b.words
            continue
        merged.append(b)
        prev_inferred = i in inferred
        prev_src = i
        prev_lines = 1
    blocks[:] = merged


def toc_from_headings(blocks: list[Block]) -> list[TocEntry]:
    heads = [b for b in blocks if b.tag in ("h1", "h2")]
    # Nest h2 under h1 only when h1s structure the whole book (parts, or h1 chapters with
    # h2 sections). Title-page and front-matter h1s alone must not swallow every chapter.
    h1_positions = [i for i, b in enumerate(heads) if b.tag == "h1"]
    has_h1 = len(h1_positions) >= 2 and h1_positions[-1] >= len(heads) // 2
    entries = []
    for n, b in enumerate(heads):
        if not b.ids:
            anchor = f"hd{n}"
            b.el.set("id", f"f{b.file_idx}-{anchor}")
            b.ids.append(anchor)
        label = text_of(b.el)
        if label:
            entries.append(TocEntry(1 if has_h1 and b.tag == "h2" else 0, label, b.file_idx, b.ids[0]))
    return entries


# --------------------------------------------------------------------------- EPUB

class Epub:
    def __init__(self, path: Path, images_dir: Path):
        self.path = path
        self.zf = zipfile.ZipFile(path)
        self.names = {n.lower(): n for n in self.zf.namelist()}
        self.images_dir = images_dir
        self.image_map: dict[str, str] = {}
        self.used_names: set[str] = set()

        container = parse_xml(self.zf.read("META-INF/container.xml"))
        rootfile = container.find(".//{*}rootfile").get("full-path")
        self.opf_dir = posixpath.dirname(rootfile)
        opf = parse_xml(self.zf.read(rootfile))
        md = opf.find("{*}metadata")

        self.title = text_of(md.find("{*}title")) if md is not None else ""
        self.title = self.title or path.stem
        self.author = ", ".join(t for t in (text_of(e) for e in md.findall("{*}creator")) if t) if md is not None else ""
        self.lang = text_of(md.find("{*}language")) if md is not None else ""

        self.items: dict[str, dict] = {}
        for it in opf.find("{*}manifest"):
            if not isinstance(it.tag, str) or it.get("href") is None:
                continue
            self.items[it.get("id")] = {
                "path": self.resolve(rootfile, it.get("href")),
                "type": it.get("media-type") or "",
                "props": (it.get("properties") or "").split(),
            }
        spine = opf.find("{*}spine")
        self.spine = [self.items[ir.get("idref")] for ir in spine.findall("{*}itemref")
                      if ir.get("idref") in self.items]
        self.ncx = self.items.get(spine.get("toc")) if spine.get("toc") else None
        if self.ncx is None:
            self.ncx = next((i for i in self.items.values() if "ncx" in i["type"]), None)
        self.nav = next((i for i in self.items.values() if "nav" in i["props"]), None)

        self.styles: dict[str, dict] = {}
        for it in self.items.values():
            if "css" in it["type"]:
                data = self.read(it["path"])
                if data:
                    parse_css_classes(data.decode("utf-8", errors="replace"), self.styles)

        cover_id = next((m.get("content") for m in md.findall("{*}meta") if m.get("name") == "cover"), None) if md is not None else None
        cover = next((i for i in self.items.values() if "cover-image" in i["props"]), None) or self.items.get(cover_id)
        self.cover_path = cover["path"] if cover and cover["type"].startswith("image/") else None

    @staticmethod
    def resolve(base_path: str, ref: str) -> str:
        ref = unquote(urlsplit(ref).path)
        return posixpath.normpath(posixpath.join(posixpath.dirname(base_path), ref))

    def read(self, zpath: str) -> bytes | None:
        name = zpath if zpath in self.zf.NameToInfo else self.names.get(zpath.lower())
        return self.zf.read(name) if name else None

    def export_resource(self, zpath: str) -> str | None:
        if zpath in self.image_map:
            return self.image_map[zpath]
        data = self.read(zpath)
        if data is None:
            return None
        base = slugify(Path(zpath).stem) + Path(zpath).suffix.lower()
        name, n = base, 1
        while name in self.used_names:
            n += 1
            name = f"{n}_{base}"
        self.used_names.add(name)
        self.images_dir.mkdir(parents=True, exist_ok=True)
        (self.images_dir / name).write_bytes(data)
        self.image_map[zpath] = f"images/{name}"
        return self.image_map[zpath]

    def rewrite_media(self, root: etree._Element, src_path: str) -> None:
        for el in list(root.iter("img", "image", "source", "video", "audio")):
            attr = "href" if el.tag == "image" else "src"
            ref = el.get(attr)
            if not ref or ref.startswith(("data:", "http:", "https:")):
                continue
            local = self.export_resource(self.resolve(src_path, ref))
            if local:
                el.set(attr, local)
            elif el.tag in ("img", "image"):
                remove_keep_tail(el)

    def toc(self, spine_paths: dict[str, int]) -> list[TocEntry]:
        entries: list[TocEntry] = []

        def add(depth: int, label: str, base: str, href: str | None) -> None:
            if not label and not href:
                return
            idx, frag = None, None
            if href:
                idx = spine_paths.get(self.resolve(base, href))
                frag = unquote(urlsplit(href).fragment) or None
            entries.append(TocEntry(depth, label or "…", idx, frag))

        if self.nav:
            root = parse_xml(self.read(self.nav["path"]))
            strip_ns(root)
            navs = list(root.iter("nav"))
            nav = next((n for n in navs if "toc" in (n.get("data-epub-type") or "")), navs[0] if navs else None)

            def walk(ol, depth):
                for li in ol.findall("li"):
                    a = li.find("a")
                    label_el = a if a is not None else li.find("span")
                    add(depth, text_of(label_el), self.nav["path"], a.get("href") if a is not None else None)
                    for sub in li.findall("ol"):
                        walk(sub, depth + 1)

            if nav is not None:
                for ol in nav.findall("ol"):
                    walk(ol, 0)
        if not entries and self.ncx:
            root = parse_xml(self.read(self.ncx["path"]))
            strip_ns(root)

            def walk_ncx(parent, depth):
                for np_ in parent.findall("navPoint"):
                    label = text_of(np_.find("navLabel"))
                    content = np_.find("content")
                    add(depth, label, self.ncx["path"], content.get("src") if content is not None else None)
                    walk_ncx(np_, depth + 1)

            nav_map = root.find(".//navMap")
            if nav_map is not None:
                walk_ncx(nav_map, 0)
        return entries


def convert_epub(src: Path, out_dir: Path, page_words: int) -> Book:
    ep = Epub(src, out_dir / "images")
    spine_paths = {item["path"]: i for i, item in enumerate(ep.spine)}
    blocks: list[Block] = []

    for idx, item in enumerate(ep.spine):
        if "html" not in item["type"] and "xml" not in item["type"]:
            continue
        data = ep.read(item["path"])
        if data is None:
            continue
        try:
            root = parse_xml(data)
        except (ValueError, etree.XMLSyntaxError) as e:
            print(f"  warning: skipping {item['path']}: {e}", file=sys.stderr)
            continue
        strip_ns(root)
        for st in root.iter("style"):
            parse_css_classes(st.text or "", ep.styles)
        etree.strip_elements(root, etree.Comment, etree.ProcessingInstruction, with_tail=False)
        etree.strip_elements(root, "script", "style", "link", "meta", "title", with_tail=False)
        ep.rewrite_media(root, item["path"])
        body = root.find(".//body")
        if body is None:
            body = root

        raw: list[etree._Element] = []
        flatten(body, raw)
        first = True
        for el in raw:
            for sub in split_block(el, page_words // 2):
                if not meaningful(sub):
                    continue
                clean_block(sub)
                b = Block(el=sub, tag=sub.tag, words=words_in(sub),
                          soft_break=first or sub.tag in SOFT_BREAK_TAGS,
                          file_idx=idx, src_path=item["path"])
                for d in sub.iter():
                    if not isinstance(d.tag, str):
                        continue
                    i = d.get("id") or (d.get("name") if d.tag == "a" else None)
                    if i:
                        b.ids.append(i)
                        d.set("id", f"f{idx}-{i}")
                        d.attrib.pop("name", None)
                blocks.append(b)
                first = False

    infer_headings(blocks, ep.styles)
    toc = ep.toc(spine_paths)
    if len({(e.file_idx, e.frag) for e in toc if e.file_idx is not None}) < 3:
        toc = toc_from_headings(blocks) or toc
    cover = ep.export_resource(ep.cover_path) if ep.cover_path else None
    return Book(title=ep.title, author=ep.author, lang=ep.lang, slug=slugify(src.stem),
                source=src.name, blocks=blocks, toc=toc, cover=cover,
                spine_paths=spine_paths, image_map=ep.image_map)


# --------------------------------------------------------------------------- PDF (best effort)

def import_fitz():
    try:
        import pymupdf as fitz        # new name
    except ImportError:
        try:
            import fitz               # old name
        except ImportError:
            sys.exit("PDF support needs PyMuPDF. Install it with: pip install pymupdf")
    return fitz


def _norm(text: str) -> str:
    return re.sub(r"\d+", "#", re.sub(r"\s+", " ", text.strip().lower()))


def _is_page_number(text: str) -> bool:
    return re.fullmatch(r"(\d{1,4}|[ivxlcdm]{1,7}|page \d+|\d+ of \d+)", text.strip().lower()) is not None


def _join_lines(lines: list[str]) -> str:
    out = ""
    for t in lines:
        if out.endswith("-") and t[:1].islower():
            out = out[:-1] + t                      # re-join a hyphenated word
        else:
            out = f"{out} {t}" if out else t
    return out


def _block_paragraphs(blk: dict) -> list[tuple[str, float]]:
    """Turn a PyMuPDF text block into paragraphs: (text, dominant font size)."""
    paras: list[tuple[str, float]] = []
    cur: list[str] = []
    cur_size = 0.0
    prev_x0 = prev_size = None

    def flush():
        nonlocal cur, cur_size
        if cur:
            paras.append((_join_lines(cur), cur_size))
        cur, cur_size = [], 0.0

    for line in blk["lines"]:
        text = "".join(s["text"] for s in line["spans"]).strip()
        if not text:
            continue
        size = max(s["size"] for s in line["spans"])
        x0 = line["bbox"][0]
        if cur and ((prev_x0 is not None and x0 - prev_x0 > 0.8 * size)     # indented first line
                    or (prev_size is not None and abs(size - prev_size) > 1.5)):  # font size jump
            flush()
        cur.append(text)
        cur_size = max(cur_size, size)
        prev_x0, prev_size = x0, size
    flush()
    return paras


def _find_tables(page, fitz) -> list[tuple[object, list[list]]]:
    if not hasattr(page, "find_tables"):
        return []
    try:
        found = page.find_tables()
    except Exception:
        return []
    out = []
    for t in found.tables:
        try:
            rows = t.extract()
        except Exception:
            continue
        if len(rows) >= 2 and max(len(r) for r in rows) >= 2:
            out.append((fitz.Rect(t.bbox), rows))
    return out


def _table_element(rows: list[list]) -> etree._Element:
    table = etree.Element("table")
    for r, row in enumerate(rows):
        tr = etree.SubElement(table, "tr")
        for cell in row:
            td = etree.SubElement(tr, "th" if r == 0 else "td")
            td.text = re.sub(r"\s+", " ", str(cell)).strip() if cell is not None else ""
    return table


def convert_pdf(src: Path, out_dir: Path, page_words: int, tables: bool = True) -> Book:
    fitz = import_fitz()
    doc = fitz.open(str(src))
    meta = doc.metadata or {}
    title = (meta.get("title") or "").strip() or src.stem
    author = (meta.get("author") or "").strip()
    images_dir = out_dir / "images"
    n_pages = doc.page_count
    no_images = fitz.TEXTFLAGS_DICT & ~fitz.TEXT_PRESERVE_IMAGES

    # Pass 1: body font size and recurring header/footer lines.
    sizes: Counter = Counter()
    edge_texts: Counter = Counter()
    for page in doc:
        h = page.rect.height
        for b in page.get_text("dict", flags=no_images)["blocks"]:
            if b["type"] != 0:
                continue
            txt = " ".join("".join(s["text"] for s in l["spans"]) for l in b["lines"])
            for l in b["lines"]:
                for s in l["spans"]:
                    sizes[round(s["size"])] += len(s["text"])
            if b["bbox"][3] < 0.12 * h or b["bbox"][1] > 0.88 * h:
                edge_texts[_norm(txt)] += 1
    body_size = sizes.most_common(1)[0][0] if sizes else 10
    hf = {t for t, c in edge_texts.items() if t and len(t) < 80 and c >= max(3, 0.25 * n_pages)}
    outline_pages: dict[int, list] = {}
    for level, t, pno in doc.get_toc():
        if pno >= 1:
            outline_pages.setdefault(pno - 1, []).append((level, t))

    # Pass 2: build blocks.
    blocks: list[Block] = []
    last_par: Block | None = None
    last_par_page = -1
    last_heading: Block | None = None
    last_heading_page = -1
    img_count = 0
    for pno, page in enumerate(doc):
        if pno and pno % 50 == 0:
            print(f"  pdf page {pno}/{n_pages}", file=sys.stderr)
        d = page.get_text("dict", sort=True)
        page_area = page.rect.get_area()
        page_has_text = any(b["type"] == 0 for b in d["blocks"])
        page_tables = _find_tables(page, fitz) if tables else []
        emitted_tables: set[int] = set()
        first_on_page = True
        first_text_on_page = True

        def emit(el, soft=False):
            nonlocal first_on_page
            b = Block(el=el, tag=el.tag, words=words_in(el), soft_break=soft, file_idx=0)
            if first_on_page:
                anchor = f"pg{pno + 1}"
                el.set("id", f"f0-{anchor}")
                b.ids.append(anchor)
                if pno in outline_pages:
                    b.soft_break = True
                first_on_page = False
            blocks.append(b)
            return b

        for blk in d["blocks"]:
            r = fitz.Rect(blk["bbox"])
            hit = next((i for i, (tr, _) in enumerate(page_tables)
                        if tr.intersects(r) and (tr & r).get_area() > 0.5 * max(r.get_area(), 1e-6)), None)
            if hit is not None:
                if hit not in emitted_tables:
                    emitted_tables.add(hit)
                    emit(_table_element(page_tables[hit][1]))
                    last_par = None
                continue
            if blk["type"] == 1:
                if (page_has_text and r.get_area() > 0.8 * page_area) or r.width < 40 or r.height < 40:
                    continue                      # scan background or decoration
                img_count += 1
                name = f"p{pno + 1:04d}_{img_count}.{blk.get('ext', 'png')}"
                images_dir.mkdir(parents=True, exist_ok=True)
                (images_dir / name).write_bytes(blk["image"])
                fig = etree.Element("figure")
                etree.SubElement(fig, "img", src=f"images/{name}", alt="")
                emit(fig)
                last_par = None
                continue
            for text, size in _block_paragraphs(blk):
                if not text.strip() or _norm(text) in hf or _is_page_number(text):
                    continue
                if size >= 1.2 * body_size and len(text.split()) <= 15:
                    level = "h1" if size >= 1.5 * body_size else "h2"
                    prev = blocks[-1] if blocks else None
                    if prev is not None and prev.tag == level and prev is last_heading and last_heading_page == pno:
                        prev.el.text = f"{prev.el.text} {text}"      # a title wrapped onto a second line
                        prev.words = words_in(prev.el)
                    else:
                        el = etree.Element(level)
                        el.text = text
                        last_heading = emit(el, soft=True)
                        last_heading_page = pno
                    last_par = None
                    first_text_on_page = False
                    continue
                if (first_text_on_page and last_par is not None and last_par_page == pno - 1
                        and blocks and blocks[-1] is last_par
                        and not ENDS_SENTENCE_RE.search(last_par.el.text or "") and text[:1].islower()):
                    last_par.el.text = _join_lines([last_par.el.text or "", text])
                    last_par.words = words_in(last_par.el)
                    first_text_on_page = False
                    continue
                el = etree.Element("p")
                el.text = text
                last_par = emit(el)
                last_par_page = pno
                first_text_on_page = False

    toc = [TocEntry(level - 1, t, 0, f"pg{pno + 1}") for pno, items in sorted(outline_pages.items()) for level, t in items]
    if not toc:
        toc = [TocEntry(0 if b.tag == "h1" else 1, text_of(b.el), 0, b.ids[0]) for b in blocks if b.tag in ("h1", "h2") and b.ids]
    cover = None
    if n_pages:
        try:
            pix = doc[0].get_pixmap(dpi=72)
            images_dir.mkdir(parents=True, exist_ok=True)
            pix.save(str(images_dir / "cover.png"))
            cover = "images/cover.png"
        except Exception:
            pass
    return Book(title=title, author=author, lang="", slug=slugify(src.stem), source=src.name,
                blocks=blocks, toc=toc, cover=cover)


# --------------------------------------------------------------------------- pagination + output

def paginate(blocks: list[Block], page_words: int, min_words: int) -> list[list[Block]]:
    pages: list[list[Block]] = []
    cur: list[Block] = []
    cw = 0
    for b in blocks:
        if b.soft_break and cur and cw >= min_words:
            pages.append(cur)
            cur, cw = [], 0
        cur.append(b)
        cw += b.words
        if cw >= page_words and b.tag not in HEADING_TAGS:
            pages.append(cur)
            cur, cw = [], 0
    if cur:
        pages.append(cur)
    if len(pages) > 1 and sum(b.words for b in pages[-1]) < min_words:
        pages[-2].extend(pages.pop())
    for n, page in enumerate(pages, 1):
        for b in page:
            b.page = n
    return pages


def page_name(n: int, total: int) -> str:
    return f"p{n:0{max(3, len(str(total)))}d}.html"


def rewrite_links(book: Book, anchor_page: dict, first_page: dict, total: int) -> None:
    for b in book.blocks:
        for a in b.el.iter("a"):
            href = a.get("href")
            if not href or "://" in href or href.startswith(("mailto:", "data:", "tel:")):
                continue
            parts = urlsplit(href)
            frag = unquote(parts.fragment) or None
            if parts.path:
                if b.src_path is None:
                    continue
                target = Epub.resolve(b.src_path, parts.path)
            else:
                target = b.src_path
            idx = book.spine_paths.get(target) if target is not None else b.file_idx
            if idx is None:
                if target in book.image_map:
                    a.set("href", book.image_map[target])
                continue
            page = anchor_page.get((idx, frag)) if frag else None
            if page is None:
                page = first_page.get(idx)
            if page is None:
                continue
            a.set("href", page_name(page, total) + (f"#f{idx}-{frag}" if frag and (idx, frag) in anchor_page else ""))


def page_label(page: list[Block], n: int) -> str:
    for b in page:
        if b.tag in HEADING_TAGS:
            t = text_of(b.el)
            if t:
                return t[:80]
    return f"Page {n}"


def html_head(title: str, lang: str, depth: int) -> str:
    rel = "../" * depth
    lang_attr = f' lang="{html.escape(lang)}"' if lang else ""
    return (f'<!DOCTYPE html>\n<html{lang_attr}>\n<head>\n<meta charset="utf-8">\n'
            f'<meta name="viewport" content="width=device-width, initial-scale=1">\n'
            f'<title>{html.escape(title)}</title>\n'
            f'<link rel="stylesheet" href="{rel}reader.css">\n<script src="{rel}reader.js"></script>\n</head>\n')


def nav_bar(n: int, total: int, label: str, bottom: bool = False) -> str:
    prev_link = f'<a class="btn" href="{page_name(n - 1, total)}" rel="prev">&larr; Prev</a>' if n > 1 else '<span class="btn disabled">&larr; Prev</span>'
    next_link = f'<a class="btn" href="{page_name(n + 1, total)}" rel="next">Next &rarr;</a>' if n < total else '<span class="btn disabled">Next &rarr;</span>'
    controls = "" if bottom else (
        '<span class="controls">'
        '<button data-action="size-" title="Smaller text">A&minus;</button>'
        '<button data-action="size+" title="Larger text">A+</button>'
        '<button data-action="line" title="Line spacing">&#8597;</button>'
        '<button data-action="width" title="Column width">&#8596;</button>'
        '<button data-action="font" title="Serif / sans-serif">Aa</button>'
        '</span>')
    return (f'<nav class="bar{" bottom" if bottom else ""}" translate="no">'
            f'<span class="group"><a class="btn" href="index.html" title="Contents">&#9776;</a>{prev_link}</span>'
            f'<span class="where"><span class="label">{html.escape(label)}</span> <span class="num">{n} / {total}</span></span>'
            f'<span class="group">{controls}{next_link}</span></nav>\n')


def write_page(book: Book, out_dir: Path, pages: list[list[Block]], n: int) -> str:
    total = len(pages)
    page = pages[n - 1]
    label = page_label(page, n)
    body = "\n".join(serialize(b.el) for b in page)
    prev_attr = f' data-prev="{page_name(n - 1, total)}"' if n > 1 else ""
    next_attr = f' data-next="{page_name(n + 1, total)}"' if n < total else ""
    doc = (html_head(f"{label} · {book.title}", book.lang, 1)
           + f'<body class="page" data-book="{book.slug}" data-page="{n}" data-label="{html.escape(label)}"{prev_attr}{next_attr}>\n'
           + nav_bar(n, total, label)
           + f'<main class="content">\n{body}\n</main>\n'
           + nav_bar(n, total, label, bottom=True)
           + "</body>\n</html>\n")
    (out_dir / page_name(n, total)).write_text(doc, encoding="utf-8")
    return label


def write_book_index(book: Book, out_dir: Path, pages: list[list[Block]], labels: list[str],
                     anchor_page: dict, first_page: dict) -> None:
    total = len(pages)
    parts = [html_head(book.title, book.lang, 1),
             f'<body class="index" data-book="{book.slug}">\n',
             '<nav class="bar" translate="no"><span class="group"><a class="btn" href="../index.html">&#9776; Library</a></span>'
             f'<span class="where"><span class="num">{total} pages</span></span><span class="group"></span></nav>\n',
             '<main class="content">\n<header class="book-head">']
    if book.cover:
        parts.append(f'<img class="cover" src="{book.cover}" alt="">')
    parts.append(f'<div><h1>{html.escape(book.title)}</h1>')
    if book.author:
        parts.append(f'<p class="author">{html.escape(book.author)}</p>')
    parts.append(f'<p class="actions"><a class="btn primary" data-continue hidden></a> '
                 f'<a class="btn" href="{page_name(1, total)}">Start from the beginning</a></p></div></header>\n')

    # Table of contents, nested by depth.
    entries = []
    for e in book.toc:
        page = None
        if e.file_idx is not None:
            page = anchor_page.get((e.file_idx, e.frag)) if e.frag else None
            if page is None:
                page = first_page.get(e.file_idx)
        href = None
        if page:
            href = page_name(page, total)
            if e.frag and (e.file_idx, e.frag) in anchor_page:
                href += f"#f{e.file_idx}-{e.frag}"
        entries.append((e.depth, e.label, href, page))
    if entries:
        parts.append("<h2>Contents</h2>\n")
        depth = -1
        for d, label, href, page in entries:
            while depth < d:
                parts.append("<ol class=\"toc\">")
                depth += 1
            while depth > d:
                parts.append("</li></ol>")
                depth -= 1
            if parts[-1] != "<ol class=\"toc\">":
                parts.append("</li>")
            inner = f'<a href="{href}">{html.escape(label)}</a>' if href else html.escape(label)
            num = f' <span class="pg">{page}</span>' if page else ""
            parts.append(f"<li>{inner}{num}")
        while depth >= 0:
            parts.append("</li></ol>")
            depth -= 1
        parts.append("\n")
    parts.append('<details class="all-pages"><summary>All pages</summary><ol class="toc">')
    for n, label in enumerate(labels, 1):
        parts.append(f'<li><a href="{page_name(n, total)}">{html.escape(label)}</a> <span class="pg">{n}</span></li>')
    parts.append("</ol></details>\n</main>\n</body>\n</html>\n")
    (out_dir / "index.html").write_text("".join(parts), encoding="utf-8")


def write_library(out_root: Path) -> None:
    books = []
    for meta in sorted(out_root.glob("*/book.json")):
        try:
            books.append(json.loads(meta.read_text(encoding="utf-8")))
        except (OSError, ValueError):
            continue
    books.sort(key=lambda b: b.get("title", "").lower())
    parts = [html_head("Library", "", 0), '<body class="library">\n',
             '<nav class="bar" translate="no"><span class="group"><span class="btn disabled">&#9776; Library</span></span>'
             f'<span class="where"><span class="num">{len(books)} books</span></span><span class="group"></span></nav>\n',
             '<main class="content">\n<h1>Library</h1>\n<ul class="books">\n']
    for b in books:
        slug = b["slug"]
        cover = f'<img class="cover" src="{slug}/{b["cover"]}" alt="">' if b.get("cover") else '<span class="cover blank"></span>'
        parts.append(f'<li><a class="cover-link" href="{slug}/index.html">{cover}</a><div>'
                     f'<a class="title" href="{slug}/index.html">{html.escape(b["title"])}</a>'
                     f'<div class="author">{html.escape(b.get("author", ""))}</div>'
                     f'<div class="meta">{b["pages"]} pages · {html.escape(b.get("source", ""))}</div>'
                     f'<a class="btn primary" data-continue data-book="{slug}" data-base="{slug}/" hidden></a></div></li>\n')
    parts.append("</ul>\n</main>\n</body>\n</html>\n")
    (out_root / "index.html").write_text("".join(parts), encoding="utf-8")


def write_shared(out_root: Path) -> None:
    (out_root / "reader.css").write_text(READER_CSS, encoding="utf-8")
    (out_root / "reader.js").write_text(READER_JS, encoding="utf-8")


def convert(src: Path, out_root: Path, page_words: int, min_words: int, tables: bool) -> dict:
    slug = slugify(src.stem)
    out_dir = out_root / slug
    if out_dir.exists():
        if not (out_dir / "book.json").exists() and any(out_dir.iterdir()):
            sys.exit(f"{out_dir} exists and does not look like babelbook output; refusing to overwrite it")
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    t0 = time.time()
    suffix = src.suffix.lower()
    if suffix == ".epub":
        book = convert_epub(src, out_dir, page_words)
    elif suffix == ".pdf":
        book = convert_pdf(src, out_dir, page_words, tables=tables)
    else:
        sys.exit(f"unsupported file type: {src}")
    if not book.blocks:
        sys.exit(f"no readable content found in {src}")

    pages = paginate(book.blocks, page_words, min_words)
    total = len(pages)
    anchor_page: dict[tuple[int, str], int] = {}
    first_page: dict[int, int] = {}
    for b in book.blocks:
        first_page.setdefault(b.file_idx, b.page)
        for i in b.ids:
            anchor_page.setdefault((b.file_idx, i), b.page)
    rewrite_links(book, anchor_page, first_page, total)

    labels = [write_page(book, out_dir, pages, n) for n in range(1, total + 1)]
    write_book_index(book, out_dir, pages, labels, anchor_page, first_page)
    meta = {"title": book.title, "author": book.author, "lang": book.lang, "slug": book.slug,
            "source": book.source, "pages": total, "cover": book.cover,
            "words": sum(b.words for b in book.blocks), "generated": time.strftime("%Y-%m-%d %H:%M:%S")}
    (out_dir / "book.json").write_text(json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
    print(f"{src.name}: {total} pages, {meta['words']:,} words, {len(list((out_dir / 'images').glob('*')) if (out_dir / 'images').exists() else [])} images"
          f" -> {out_dir}  ({time.time() - t0:.1f}s)")
    return meta


def serve(out_root: Path, host: str, port: int, open_url: str | None) -> None:
    handler = partial(http.server.SimpleHTTPRequestHandler, directory=str(out_root))
    http.server.SimpleHTTPRequestHandler.log_message = lambda *a, **k: None   # quiet
    srv = http.server.ThreadingHTTPServer((host, port), handler)
    shown = "localhost" if host in ("127.0.0.1", "0.0.0.0", "") else host
    url = f"http://{shown}:{port}/"
    print(f"serving {out_root} at {url}  (Ctrl-C to stop)")
    if open_url:
        webbrowser.open(url + open_url)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("books", nargs="*", type=Path, help="EPUB or PDF files to convert")
    p.add_argument("--out-root", type=Path, default=DEFAULT_OUT_ROOT, help=f"where the HTML goes (default {DEFAULT_OUT_ROOT})")
    p.add_argument("--page-words", type=int, default=2000, help="target words per page (default 2000)")
    p.add_argument("--min-words", type=int, default=300, help="never start a new page at a chapter break before this many words (default 300)")
    p.add_argument("--no-tables", action="store_true", help="PDF: skip table detection (faster)")
    p.add_argument("--serve", action="store_true", help="after converting, serve the output folder over HTTP")
    p.add_argument("--host", default="127.0.0.1", help="--serve bind address; 0.0.0.0 to reach it from other devices")
    p.add_argument("--port", type=int, default=8000)
    p.add_argument("--open", action="store_true", help="with --serve, open the browser")
    args = p.parse_args()
    if not args.books and not args.serve:
        p.error("give at least one .epub/.pdf, or --serve")

    out_root = args.out_root.expanduser()
    out_root.mkdir(parents=True, exist_ok=True)
    write_shared(out_root)
    last = None
    for src in args.books:
        src = src.expanduser()
        if not src.is_file():
            sys.exit(f"not a file: {src}")
        last = convert(src, out_root, args.page_words, args.min_words, tables=not args.no_tables)
    write_library(out_root)
    if args.serve:
        serve(out_root, args.host, args.port, (f"{last['slug']}/index.html" if last else "") if args.open else None)
    elif last:
        print(f"open {out_root / 'index.html'} or run: {Path(sys.argv[0]).name} --serve")
    return 0


# --------------------------------------------------------------------------- shared reader assets

READER_CSS = """\
:root {
  --font-size: 20px; --line-height: 1.6; --width: 42rem;
  --bg: #fdfdfb; --fg: #1b1b1b; --muted: #6b6b6b; --bar: #f1f1ee; --rule: #d9d9d4; --link: #1a56a8; --accent: #2b6cb0;
}
@media (prefers-color-scheme: dark) {
  :root { --bg: #141414; --fg: #e6e6e3; --muted: #9a9a9a; --bar: #1f1f1f; --rule: #333; --link: #8ab4f8; --accent: #6ea8f0; }
}
html { background: var(--bg); color: var(--fg); font-size: var(--font-size); line-height: var(--line-height);
       font-family: Georgia, "Noto Serif", "Noto Serif CJK KR", "Times New Roman", serif; }
html[data-font="sans"] { font-family: system-ui, -apple-system, "Segoe UI", "Noto Sans", "Noto Sans CJK KR", sans-serif; }
body { margin: 0; }
[hidden] { display: none !important; }
a { color: var(--link); }
main.content { max-width: var(--width); margin: 0 auto; padding: 1.5rem 1rem 4rem; overflow-wrap: break-word; }
main p { margin: 0 0 1em; }
main h1, main h2, main h3, main h4 { line-height: 1.25; margin: 1.6em 0 .6em; }
main h1 { font-size: 1.7em; } main h2 { font-size: 1.4em; } main h3 { font-size: 1.15em; }
main img, main svg, main video { max-width: 100%; height: auto; }
main > img, main figure img { display: block; margin: 1em auto; }
main figure { margin: 1.5em 0; text-align: center; }
main figcaption { font-size: .85em; color: var(--muted); }
main blockquote { margin: 1em 0 1em 1.5em; padding-left: 1em; border-left: 3px solid var(--rule); }
main pre { white-space: pre-wrap; overflow-x: auto; font-size: .9em; }
main hr { border: 0; border-top: 1px solid var(--rule); margin: 2em auto; width: 40%; }
.table-wrap { overflow-x: auto; margin: 1em 0; }
main table { border-collapse: collapse; font-size: .9em; margin: 0 auto; }
main td, main th { border: 1px solid var(--rule); padding: .3em .6em; vertical-align: top; }
main th { background: var(--bar); }

/* reader chrome: fixed pixel sizes so the A+/A- buttons do not scale it */
.bar { position: sticky; top: 0; z-index: 10; display: flex; align-items: center; justify-content: space-between; gap: .5rem;
       padding: 6px 10px; background: var(--bar); border-bottom: 1px solid var(--rule); font: 14px/1.3 system-ui, sans-serif; }
.bar.bottom { position: static; border-top: 1px solid var(--rule); border-bottom: 0; }
.bar .group { display: flex; align-items: center; gap: 6px; }
.bar .where { flex: 1; text-align: center; color: var(--muted); min-width: 0; }
.bar .label { display: inline-block; max-width: 40vw; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; vertical-align: bottom; }
.bar .num { white-space: nowrap; }
.btn, .bar button { display: inline-block; padding: 4px 10px; border: 1px solid var(--rule); border-radius: 6px; background: var(--bg);
       color: var(--fg); text-decoration: none; font: 14px/1.3 system-ui, sans-serif; cursor: pointer; }
.btn.disabled { opacity: .4; cursor: default; }
.btn.primary { background: var(--accent); border-color: var(--accent); color: #fff; }
.bar button:hover, .btn:hover { border-color: var(--accent); }
.controls { display: none; gap: 4px; }
@media (min-width: 560px) { .controls { display: inline-flex; } }

/* book and library pages */
.book-head { display: flex; gap: 1.5rem; align-items: flex-start; margin-bottom: 1.5rem; }
.book-head .cover { width: 140px; max-width: 30vw; height: auto; box-shadow: 0 2px 10px rgba(0,0,0,.25); }
.book-head h1 { margin: 0 0 .3em; }
.author { color: var(--muted); margin: 0 0 1em; }
.actions .btn { margin-right: .5rem; }
ol.toc { padding-left: 1.4em; } ol.toc li { margin: .25em 0; } ol.toc .pg { color: var(--muted); font-size: .8em; margin-left: .4em; }
details.all-pages { margin-top: 2em; } details.all-pages summary { cursor: pointer; color: var(--muted); }
ul.books { list-style: none; padding: 0; }
ul.books li { display: flex; gap: 1rem; align-items: flex-start; padding: 1rem 0; border-bottom: 1px solid var(--rule); }
ul.books .cover { width: 90px; height: auto; display: block; box-shadow: 0 2px 8px rgba(0,0,0,.25); }
ul.books .cover.blank { width: 90px; height: 130px; background: var(--bar); }
ul.books .title { font-size: 1.1em; font-weight: 600; text-decoration: none; }
ul.books .meta { color: var(--muted); font-size: .85em; margin: .3em 0 .6em; }
"""

READER_JS = """\
// Runs in <head> so saved settings apply before the first paint.
(function () {
  var SETTINGS = 'reader:settings';
  var defaults = { size: 20, line: 1.6, width: 42, font: 'serif' };
  var LINES = [1.4, 1.6, 1.8, 2.0], WIDTHS = [34, 42, 50, 62];
  var s = defaults;
  function load() { try { s = Object.assign({}, defaults, JSON.parse(localStorage.getItem(SETTINGS) || '{}')); } catch (e) { s = Object.assign({}, defaults); } }
  function save() { try { localStorage.setItem(SETTINGS, JSON.stringify(s)); } catch (e) {} }
  function apply() {
    var r = document.documentElement;
    r.style.setProperty('--font-size', s.size + 'px');
    r.style.setProperty('--line-height', s.line);
    r.style.setProperty('--width', s.width + 'rem');
    r.setAttribute('data-font', s.font);
  }
  function cycle(list, cur) { var i = list.indexOf(cur); return list[(i + 1) % list.length]; }
  function getLast(book) { try { return JSON.parse(localStorage.getItem('reader:last:' + book) || 'null'); } catch (e) { return null; } }
  function setLast(book, v) { try { localStorage.setItem('reader:last:' + book, JSON.stringify(v)); } catch (e) {} }

  load(); apply();

  document.addEventListener('DOMContentLoaded', function () {
    var body = document.body, book = body.dataset.book, page = body.dataset.page;

    // Font controls.
    Array.prototype.forEach.call(document.querySelectorAll('[data-action]'), function (btn) {
      btn.addEventListener('click', function () {
        switch (btn.dataset.action) {
          case 'size+': s.size = Math.min(40, s.size + 2); break;
          case 'size-': s.size = Math.max(12, s.size - 2); break;
          case 'line': s.line = cycle(LINES, s.line); break;
          case 'width': s.width = cycle(WIDTHS, s.width); break;
          case 'font': s.font = s.font === 'serif' ? 'sans' : 'serif'; break;
        }
        apply(); save();
      });
    });

    // Remember where you are: page + scroll offset, per book.
    if (book && page) {
      var here = location.pathname.split('/').pop();
      var prev = getLast(book);
      if (prev && prev.page === here && prev.y > 0) {
        window.addEventListener('load', function () { window.scrollTo(0, prev.y); });
      }
      var rec = { page: here, label: body.dataset.label || '', num: page, y: 0 };
      setLast(book, rec);
      var t = null;
      window.addEventListener('scroll', function () {
        if (t) return;
        t = setTimeout(function () { t = null; rec.y = window.scrollY; setLast(book, rec); }, 300);
      }, { passive: true });

      // Arrow keys turn pages.
      document.addEventListener('keydown', function (e) {
        if (e.altKey || e.ctrlKey || e.metaKey) return;
        if (e.key === 'ArrowRight' && body.dataset.next) location.href = body.dataset.next;
        if (e.key === 'ArrowLeft' && body.dataset.prev) location.href = body.dataset.prev;
      });
    }

    // "Continue reading" links on the book page and in the library.
    Array.prototype.forEach.call(document.querySelectorAll('[data-continue]'), function (a) {
      var b = a.dataset.book || book, base = a.dataset.base || '';
      var last = b && getLast(b);
      if (!last || !last.page) return;
      a.href = base + last.page;
      a.textContent = 'Continue: ' + (last.label || 'page ' + last.num) + ' (' + last.num + ')';
      a.hidden = false;
    });
  });
})();
"""


if __name__ == "__main__":
    sys.exit(main())
