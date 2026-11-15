#!/usr/bin/env python3
"""Render a design memo from ONE Markdown source to HTML and PDF.

    python3 scripts/build_design_pdf.py IN.md OUT.html OUT.pdf

The Markdown is canonical; both renderings are generated, so a number cannot
drift between the page and the print. Markdown subset: `#`/`##`/`###` headings,
paragraphs, *italic* / **bold** / `code`, `-` bullets, `1.` numbered lists,
`| pipe | tables |`, `---` rules.

Machine notes (measured 2026-08-28): this Mac has no pandoc, wkhtmltopdf,
weasyprint, Chrome or LaTeX, so the PDF goes through reportlab. The body font is
`Arial Unicode` because plain Arial has no glyph for `≅`, `∧` or `∥`, and code
spans fall back to it when Courier New lacks a glyph (∀, Π, λ). Preview a page
with `qlmanage -t -s 1400 -o <dir> OUT.pdf` (the usual pdftoppm is absent).
The HTML is theme-aware and is what gets published as the artifact page.
"""
import html as _html
import os
import re
import sys

SRC, OUT_HTML, OUT_PDF = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(SRC, encoding="utf-8").read().splitlines()

# ---------- parse into blocks ----------
blocks = []  # (kind, payload)
i = 0
para = []


def flush_para():
    global para
    if para:
        blocks.append(("p", " ".join(s.strip() for s in para)))
        para = []


while i < len(lines):
    ln = lines[i]
    s = ln.strip()
    if not s:
        flush_para(); i += 1; continue
    m = re.match(r"^(#{1,3})\s+(.*)$", s)
    if m:
        flush_para(); blocks.append(("h%d" % len(m.group(1)), m.group(2).strip())); i += 1; continue
    if s == "---":
        flush_para(); blocks.append(("hr", None)); i += 1; continue
    if s.startswith("|"):
        flush_para()
        rows = []
        while i < len(lines) and lines[i].strip().startswith("|"):
            r = lines[i].strip().strip("|")
            cells = [c.strip() for c in r.split("|")]
            if not all(re.fullmatch(r":?-{2,}:?", c) for c in cells):
                rows.append(cells)
            i += 1
        blocks.append(("table", rows)); continue
    if re.match(r"^[-*]\s+", s):
        flush_para(); items = []
        while i < len(lines) and re.match(r"^\s*[-*]\s+", lines[i]):
            items.append(re.sub(r"^\s*[-*]\s+", "", lines[i]).strip()); i += 1
        blocks.append(("ul", items)); continue
    if re.match(r"^\d+\.\s+", s):
        flush_para(); items = []
        while i < len(lines) and re.match(r"^\s*\d+\.\s+", lines[i]):
            items.append(re.sub(r"^\s*\d+\.\s+", "", lines[i]).strip()); i += 1
        blocks.append(("ol", items)); continue
    para.append(ln); i += 1
flush_para()

title = next((p for k, p in blocks if k == "h1"), "Document")
subtitle = ""
for k, p in blocks[1:3]:
    if k == "p" and p.startswith("*") and p.endswith("*"):
        subtitle = p.strip("*"); break

# ---------- inline formatting ----------
def inline_html(t):
    t = _html.escape(t, quote=False)
    t = re.sub(r"`([^`]+)`", r"<code>\1</code>", t)
    t = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", t)
    t = re.sub(r"(?<![\w*])\*([^*]+)\*(?![\w*])", r"<i>\1</i>", t)
    return t


_MONO_FACE = None


def _mono_safe(s):
    """True when Courier New has a glyph for every character in `s`.

    Courier New lacks the logical/mathematical glyphs a Lean-shaped memo uses
    (∀, Π, λ, ≅). A span containing one is set in the Unicode body face instead
    of silently rendering as tofu boxes.
    """
    global _MONO_FACE
    if _MONO_FACE is None:
        _MONO_FACE = pdfmetrics.getFont("Mono").face
    return all(ord(c) in _MONO_FACE.charToGlyph for c in s)


def inline_pdf(t):
    t = _html.escape(t, quote=False)
    t = re.sub(
        r"`([^`]+)`",
        lambda m: '<font face="%s" size="8.2">%s</font>'
        % ("Mono" if _mono_safe(m.group(1)) else "Body", m.group(1)),
        t,
    )
    t = re.sub(r"\*\*([^*]+)\*\*", r"<b>\1</b>", t)
    t = re.sub(r"(?<![\w*])\*([^*]+)\*(?![\w*])", r"<i>\1</i>", t)
    return t

# ---------- HTML ----------
CSS = """
:root{--bg:#F4F5F7;--surface:#FFFFFF;--ink:#171A1F;--ink-2:#3D4450;--muted:#6B7380;--rule:#D3D8E0;--rule-2:#E6E9EE;--accent:#0E5A6C;--accent-ink:#0B4553;--accent-soft:#DCEEF2;--code-bg:#EEF1F5}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#111316;--surface:#181B20;--ink:#E7E9EC;--ink-2:#C3C8CF;--muted:#8E97A3;--rule:#2C323A;--rule-2:#23282F;--accent:#63BCCF;--accent-ink:#8ED2E0;--accent-soft:#14333B;--code-bg:#1F242B}}
:root[data-theme="dark"]{--bg:#111316;--surface:#181B20;--ink:#E7E9EC;--ink-2:#C3C8CF;--muted:#8E97A3;--rule:#2C323A;--rule-2:#23282F;--accent:#63BCCF;--accent-ink:#8ED2E0;--accent-soft:#14333B;--code-bg:#1F242B}
html{background:var(--bg)} body{margin:0;background:var(--bg);color:var(--ink);font-family:"IBM Plex Sans",system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;font-size:16px;line-height:1.55;-webkit-font-smoothing:antialiased}
.page{max-width:960px;margin:0 auto;padding:44px 24px 96px}
h1,h2,h3{font-family:"IBM Plex Sans Condensed","IBM Plex Sans",system-ui,sans-serif;font-weight:700;letter-spacing:-.01em;text-wrap:balance;margin:0}
h1{font-size:2.4rem;line-height:1.08} h2{font-size:1.45rem;line-height:1.2;margin-top:52px;padding-top:18px;border-top:1px solid var(--rule)} h3{font-size:1.08rem;margin-top:28px}
p{max-width:72ch;margin:12px 0} p.sub{font-size:1.12rem;color:var(--ink-2);max-width:66ch;margin-top:10px} p.meta{color:var(--muted);font-size:.9rem;max-width:80ch}
code{font-family:"IBM Plex Mono",ui-monospace,SFMono-Regular,Menlo,monospace;font-size:.86em;background:var(--code-bg);padding:1px 5px;border-radius:3px}
ul,ol{max-width:76ch;padding-left:22px} li{margin:6px 0}
.tablewrap{overflow-x:auto;margin:16px 0;border:1px solid var(--rule);border-radius:8px;background:var(--surface)}
table{border-collapse:collapse;width:100%;font-size:.9rem} th,td{text-align:left;vertical-align:top;padding:9px 12px;border-bottom:1px solid var(--rule-2)}
th{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:.72rem;letter-spacing:.06em;text-transform:uppercase;color:var(--muted);font-weight:500;background:var(--bg)} tr:last-child td{border-bottom:none}
td.num,th.num{text-align:right;font-variant-numeric:tabular-nums;white-space:nowrap;font-family:"IBM Plex Mono",monospace;font-size:.86rem}
hr{border:none;border-top:1px solid var(--rule);margin:28px 0}
.decision{background:var(--surface);border:1px solid var(--rule);border-left:4px solid var(--accent);border-radius:0 8px 8px 0;padding:6px 20px 12px;margin-top:22px}
.decision p{max-width:76ch}
a:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
"""

out = []
out.append("<title>%s</title>" % _html.escape(title))
out.append('<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans+Condensed:wght@600;700&family=IBM+Plex+Sans:ital,wght@0,400;0,500;0,600;1,400&family=IBM+Plex+Mono:wght@400;500&display=swap">')
out.append("<style>%s</style>" % CSS)
out.append('<div class="page">')
in_decision = False
first_h2_seen = False
for k, p in blocks:
    if k == "h1":
        out.append("<h1>%s</h1>" % inline_html(p)); continue
    if k == "p" and p.startswith("*") and p.endswith("*") and not first_h2_seen and p.strip("*") == subtitle:
        out.append('<p class="sub">%s</p>' % inline_html(p.strip("*"))); continue
    if k == "p" and not first_h2_seen:
        out.append('<p class="meta">%s</p>' % inline_html(p)); continue
    if k == "h2":
        if in_decision:
            out.append("</div>"); in_decision = False
        first_h2_seen = True
        out.append("<h2>%s</h2>" % inline_html(p))
        if p.startswith("The decision"):
            out.append('<div class="decision">'); in_decision = True
        continue
    if k == "h3":
        out.append("<h3>%s</h3>" % inline_html(p)); continue
    if k == "p":
        out.append("<p>%s</p>" % inline_html(p)); continue
    if k == "hr":
        out.append("<hr>"); continue
    if k in ("ul", "ol"):
        out.append("<%s>%s</%s>" % (k, "".join("<li>%s</li>" % inline_html(x) for x in p), k)); continue
    if k == "table":
        hdr, body = p[0], p[1:]
        numcols = {j for j in range(len(hdr)) if hdr[j].strip().lower() in ("low", "high", "lane-days", "full row", "stage 1 slice")}
        h = "".join('<th%s>%s</th>' % (' class="num"' if j in numcols else "", inline_html(c)) for j, c in enumerate(hdr))
        rows = []
        for r in body:
            rows.append("<tr>%s</tr>" % "".join('<td%s>%s</td>' % (' class="num"' if j in numcols else "", inline_html(c)) for j, c in enumerate(r)))
        out.append('<div class="tablewrap"><table><thead><tr>%s</tr></thead><tbody>%s</tbody></table></div>' % (h, "".join(rows)))
if in_decision:
    out.append("</div>")
out.append("</div>")
open(OUT_HTML, "w", encoding="utf-8").write("\n".join(out) + "\n")

# ---------- PDF ----------
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import inch
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (KeepTogether, ListFlowable, ListItem, PageBreak, Paragraph,
                                SimpleDocTemplate, Spacer, Table, TableStyle, HRFlowable)

FONTS = {
    "Body": "/System/Library/Fonts/Supplemental/Arial Unicode.ttf",
    "BodyB": "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
    "BodyI": "/System/Library/Fonts/Supplemental/Arial Italic.ttf",
    "Mono": "/System/Library/Fonts/Supplemental/Courier New.ttf",
}
for name, path in FONTS.items():
    pdfmetrics.registerFont(TTFont(name, path))
pdfmetrics.registerFontFamily("Body", normal="Body", bold="BodyB", italic="BodyI", boldItalic="BodyB")

INK = colors.HexColor("#171A1F"); INK2 = colors.HexColor("#3D4450"); MUTED = colors.HexColor("#6B7380")
ACCENT = colors.HexColor("#0E5A6C"); RULE = colors.HexColor("#D3D8E0"); RULE2 = colors.HexColor("#E6E9EE"); SOFT = colors.HexColor("#F4F5F7")

st = {
    "h1": ParagraphStyle("h1", fontName="BodyB", fontSize=24, leading=28, textColor=INK, spaceAfter=6),
    "sub": ParagraphStyle("sub", fontName="BodyI", fontSize=11.5, leading=15, textColor=INK2, spaceAfter=8),
    "meta": ParagraphStyle("meta", fontName="Body", fontSize=8.8, leading=12, textColor=MUTED, spaceAfter=10),
    "h2": ParagraphStyle("h2", fontName="BodyB", fontSize=15, leading=18, textColor=INK, spaceBefore=18, spaceAfter=6),
    "h3": ParagraphStyle("h3", fontName="BodyB", fontSize=11.5, leading=14, textColor=INK, spaceBefore=12, spaceAfter=4),
    "p": ParagraphStyle("p", fontName="Body", fontSize=9.6, leading=13.4, textColor=INK, spaceAfter=6, alignment=TA_LEFT),
    "li": ParagraphStyle("li", fontName="Body", fontSize=9.6, leading=13.2, textColor=INK),
    "cell": ParagraphStyle("cell", fontName="Body", fontSize=7.6, leading=9.6, textColor=INK),
    "cellh": ParagraphStyle("cellh", fontName="BodyB", fontSize=7.2, leading=9, textColor=MUTED),
}

story = []
first_h2_seen = False


def cell(t, style="cell"):
    return Paragraph(inline_pdf(t), st[style])


for k, p in blocks:
    if k == "h1":
        story.append(Paragraph(inline_pdf(p), st["h1"])); continue
    if k == "p" and p.startswith("*") and p.endswith("*") and not first_h2_seen and p.strip("*") == subtitle:
        story.append(Paragraph(inline_pdf(p.strip("*")), st["sub"])); continue
    if k == "p" and not first_h2_seen:
        story.append(Paragraph(inline_pdf(p), st["meta"]))
        story.append(HRFlowable(width="100%", thickness=0.6, color=RULE, spaceBefore=2, spaceAfter=8)); continue
    if k == "h2":
        first_h2_seen = True
        story.append(HRFlowable(width="100%", thickness=0.5, color=RULE, spaceBefore=10, spaceAfter=0))
        story.append(Paragraph(inline_pdf(p), st["h2"])); continue
    if k == "h3":
        story.append(Paragraph(inline_pdf(p), st["h3"])); continue
    if k == "p":
        story.append(Paragraph(inline_pdf(p), st["p"])); continue
    if k == "hr":
        story.append(HRFlowable(width="100%", thickness=0.5, color=RULE, spaceBefore=8, spaceAfter=8)); continue
    if k in ("ul", "ol"):
        items = [ListItem(Paragraph(inline_pdf(x), st["li"]), leftIndent=14) for x in p]
        story.append(ListFlowable(items, bulletType="1" if k == "ol" else "bullet", start="1" if k == "ol" else None,
                                  bulletFontName="Body", bulletFontSize=8.5, leftIndent=14, spaceAfter=6))
        continue
    if k == "table":
        hdr, body = p[0], p[1:]
        ncol = len(hdr)
        # column width heuristic: proportional to average cell length, clamped
        lens = [max(8, sum(len(r[j]) if j < len(r) else 0 for r in body) / max(1, len(body))) for j in range(ncol)]
        lens = [min(max(l, 14), 70) for l in lens]
        # narrow numeric/id columns
        for j, h in enumerate(hdr):
            if h.strip().lower() in ("low", "high", "conf.", "id", "gate", "full row", "stage 1 slice"):
                lens[j] = min(lens[j], 10)
        total = sum(lens); avail = 7.0 * inch
        widths = [avail * l / total for l in lens]
        data = [[cell(c, "cellh") for c in hdr]] + [[cell(r[j] if j < len(r) else "") for j in range(ncol)] for r in body]
        tbl = Table(data, colWidths=widths, repeatRows=1, hAlign="LEFT")
        tbl.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, 0), SOFT),
            ("LINEBELOW", (0, 0), (-1, 0), 0.6, RULE),
            ("LINEBELOW", (0, 1), (-1, -1), 0.3, RULE2),
            ("BOX", (0, 0), (-1, -1), 0.5, RULE),
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("LEFTPADDING", (0, 0), (-1, -1), 4), ("RIGHTPADDING", (0, 0), (-1, -1), 4),
            ("TOPPADDING", (0, 0), (-1, -1), 3), ("BOTTOMPADDING", (0, 0), (-1, -1), 3),
        ]))
        story.append(tbl); story.append(Spacer(1, 8)); continue


def on_page(canvas, doc):
    canvas.saveState()
    canvas.setFont("Body", 7.5); canvas.setFillColor(MUTED)
    canvas.drawString(0.75 * inch, 0.5 * inch, title)
    canvas.drawRightString(letter[0] - 0.75 * inch, 0.5 * inch, "page %d" % doc.page)
    canvas.restoreState()


doc = SimpleDocTemplate(OUT_PDF, pagesize=letter, leftMargin=0.75 * inch, rightMargin=0.75 * inch,
                        topMargin=0.7 * inch, bottomMargin=0.75 * inch, title=title, author="Clean × Trust sizing memo")
doc.build(story, onFirstPage=on_page, onLaterPages=on_page)
print("html", os.path.getsize(OUT_HTML), "bytes; pdf", os.path.getsize(OUT_PDF), "bytes")
