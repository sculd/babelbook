# babelbook

Read EPUB (and, best effort, PDF) books in a web browser so the browser's
built-in translation can translate them. `babelbook.py` turns a book into a
folder of plain HTML pages plus a small library page, and can serve it locally.

## Why it is built this way

- **One real HTML file per page.** Browser translation (Chrome, Firefox) is most
  reliable on a freshly loaded page. Readers that swap chapter content inside one
  page or an iframe are translated unreliably. With "always translate English"
  turned on, every page you navigate to is translated automatically.
- **Pages are cut by amount of text, not by screen size.** About 2000 words per
  page, split only at paragraph boundaries, never inside a table, figure or list
  item, and a new page at every chapter. Changing the font size therefore never
  requires re-pagination; you just scroll a little more.
- **Images and tables come through as-is** from EPUBs. The book's own CSS is
  dropped in favour of one clean, readable stylesheet.

## Usage

Needs Python 3.10+ with `lxml`; PDF additionally needs `pymupdf`.

```bash
pip install -r requirements.txt            # or use an existing venv that has lxml

# convert; output goes to ~/babelbook_html/<book>/ (change with --out-root)
python babelbook.py epubs/alice.epub
python babelbook.py epubs/*.epub some-book.pdf

# convert and serve on http://localhost:8000 (--open opens the browser)
python babelbook.py epubs/alice.epub --serve --open

# just serve what is already converted
python babelbook.py --serve
python babelbook.py --serve --host 0.0.0.0 --port 8000   # reachable from phone/tablet on LAN or Tailscale
```

Options:

```
--out-root DIR      where the HTML goes (default ~/babelbook_html)
--page-words N      target words per page (default 2000)
--min-words N       no chapter page break before this many words (default 300)
--no-tables         PDF: skip table detection (faster)
```

Output layout:

```
~/babelbook_html/index.html              library: every converted book
~/babelbook_html/reader.css, reader.js   shared reader chrome
~/babelbook_html/<slug>/index.html       book page: cover, contents, "continue reading"
~/babelbook_html/<slug>/p001.html ...    the pages
~/babelbook_html/<slug>/images/          images from the book
~/babelbook_html/<slug>/book.json        metadata for the library page
```

## Reader

Prev/next links and arrow keys; A−/A+ font size, line spacing, column width and
serif/sans toggle, remembered in localStorage for all books; per-book "continue
reading" that remembers the page and scroll position. Settings and positions are
stored per browser origin, so pick one way of opening the output (file:// or
http://localhost:PORT) and stick with it.

Translation in Chrome: open a page, click the translate icon in the address bar,
pick the target language and tick "Always translate English".

## How books are handled

**EPUB.** Spine files are parsed with lxml, wrapper divs are flattened into a
list of blocks, images are copied out, internal links and footnote anchors are
rewritten to the page that holds the target. Long lists, long blockquotes and
huge `<br>`-separated paragraphs (an index, a poem) are split so a page can end
inside them; a genuinely long paragraph stays whole. Books without heading tags
(Calibre output, many publishers) get headings inferred from the book's CSS font
sizes, a chapter label line ("VI", "Part Two") is merged with the title line
after it, and a table of contents is built from the headings when the book's own
is missing or trivial.

**PDF (best effort, PyMuPDF).** Paragraphs are rebuilt from text lines
(indentation and font-size changes start a new one, hyphenated words are
rejoined, a paragraph continues across a page break); running headers, footers
and page numbers are dropped; headings are guessed from font size; embedded
images are extracted; ruled tables are detected. Two-column layouts and scanned
PDFs without a text layer come out poorly.

## Test books

`epubs/` holds test books and is git-ignored (not every book in there is public
domain). Public-domain sources used:

- Project Gutenberg. The main site returns 403 to scripted downloads from some
  networks; the official mirror works: `https://gutenberg.pglaf.org/cache/epub/<id>/pg<id>-images-3.epub`
  (alice #11, alice_tenniel #28885, origin #1228, wealth #3300).
- Standard Ebooks. Append `?source=download` to the download link to get the file
  instead of the interstitial page (pride = Jane Austen, Pride and Prejudice).

## License

MIT. Note that the optional PDF path uses PyMuPDF, which is licensed under the
AGPL-3.0; that only matters if you redistribute babelbook together with PyMuPDF
or offer it as a network service, not for local use.
