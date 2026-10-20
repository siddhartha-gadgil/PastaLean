#!/usr/bin/env python3
"""Render pastalean.md into a standalone HTML page.

Writes index.html next to snippets/, so `python3 -m http.server` in this folder
serves the whole post. Nothing else is needed: the snippets are self-contained.

A ```lean block followed by `<!-- interactive: snippets/x.html -->` is replaced by
that snippet in an iframe; the iframe reports its height and takes the page's theme
(see snippets/embed_postprocess.py for the other half of that bridge).
"""
import argparse, html, re, pathlib

HERE = pathlib.Path(__file__).resolve().parent
SRC = HERE / 'pastalean.md'
TPL = HERE / 'site'

MAST = '''<header class="mast">
  <p class="eyebrow">Python &rarr; Lean 4</p>
  <h1>{title}</h1>
  <p class="standfirst">A deterministic transpiler, the seven design decisions behind it, and why the
  translation step is the one place a language model must not be.</p>
  <p class="byline"><span>By <b>Anirudh Gupta</b></span><span>17 October 2026</span><span>~25 min read</span></p>
</header>

<main>'''

NOTATION = '''<div class="notation">
  <h4>Two bits of notation, so the code reads</h4>
  <dl>
    <dt>+&#8346; &nbsp;%&#8346; &nbsp;//&#8346;</dt>
    <dd>An operator with <em>Python's</em> meaning rather than Lean's. The subscript p is the whole
        point of the runtime: <code>7 //&#8346; -2</code> is <code>-4</code>, as Python says, where
        Lean's own division would give <code>-3</code>.</dd>
    <dt>&#10835;P&#10836; prog &#10835;Q&#10836;</dt>
    <dd>A Hoare triple, read as a sentence: <em>assuming P holds, running prog leaves Q true.</em>
        P comes from <code>Requires</code> in the Python, Q from <code>Ensures</code>.</dd>
  </dl>
</div>'''

FOOT = '''</main>
<footer>
  <p>PastaLean is open source at <a href="https://github.com/siddhartha-gadgil/PastaLean">github.com/siddhartha-gadgil/PastaLean</a>.
  Every Lean block on this page is real generated output, rendered with
  <a href="https://github.com/AnirudhG07/verso-snippets">verso-snippets</a> &mdash; which renders only
  Lean that compiles, so the code here has been checked by the same elaborator the project relies on.</p>
</footer>'''

TOGGLE = '''<button id="themebtn" class="themebtn" type="button" aria-label="Switch between light and dark">
  <span data-when="light">Dark</span><span data-when="dark">Light</span></button>
<script>
(function () {
  var root = document.documentElement, btn = document.getElementById('themebtn');
  function osDark() {
    try { return window.matchMedia('(prefers-color-scheme: dark)').matches; } catch (e) { return false; }
  }
  var saved = null;
  try { saved = localStorage.getItem('pastalean-blog-theme'); } catch (e) {}
  function set(t) {
    root.setAttribute('data-theme', t);
    try { localStorage.setItem('pastalean-blog-theme', t); } catch (e) {}
  }
  set(saved === 'dark' || saved === 'light' ? saved : (osDark() ? 'dark' : 'light'));
  btn.addEventListener('click', function () {
    set(root.getAttribute('data-theme') === 'dark' ? 'light' : 'dark');
  });
})();
</script>'''


# The paper's appendix works five HumanEval problems end to end; these are the two
# hardest. Python comes from the committed contract file, the proof from the rendered
# snippet of PastaBench/humaneval/<dir>/Proofs.lean.
EXAMPLES = [
    dict(key='count_up_to',
         label='count_up_to — a prime sieve (HumanEval/96)',
         py='PastaBench/humaneval/CountUpTo/solution_contracts.py',
         snippet='snippets/ex_count_up_to.html',
         note='Nested loops. Six invariants on the outer loop and two on the inner, and from '
              'them three postconditions: the answer is no longer than n, and every entry lies '
              'in the window 2 … n-1.'),
    dict(key='double_the_difference',
         label='double_the_difference — a function restated as a sum (HumanEval/151)',
         py='PastaBench/humaneval/DoubleTheDifference/solution_contracts.py',
         snippet='snippets/ex_double_the_difference.html',
         note='The postcondition restates the entire function as a summation, so proving it '
              'means proving the loop computes that sum and nothing else. The heaviest of the '
              "paper's five."),
]


def explorer():
    opts, panels = [], []
    for n, ex in enumerate(EXAMPLES):
        opts.append(f'<option value="{ex["key"]}">{html.escape(ex["label"])}</option>')
        src = (HERE.parents[1] / ex['py']).read_text().rstrip()
        snip = HERE / ex['snippet']
        v = f'?v={int(snip.stat().st_mtime)}' if snip.exists() else ''
        panels.append(
            f'<section class="ex" id="ex-{ex["key"]}"{"" if n == 0 else " hidden"}>'
            f'<p class="exnote">{html.escape(ex["note"])}</p>'
            f'<h4>1 &middot; The Python, carrying its contract</h4>'
            f'<div class="codeblock"><span class="codelab">Python</span><pre>'
            f'<code class="language-python">{html.escape(src)}</code></pre></div>'
            f'<h4>2 &middot; The Lean it becomes, and the proof that closes it</h4>'
            f'<div class="snipwrap"><iframe class="snip" loading="lazy" src="{ex["snippet"]}{v}" '
            f'title="Lean translation and proof"></iframe></div></section>')
    return ('<div class="explorer"><label for="exsel">Explore a proved problem:</label> '
            f'<select id="exsel">{"".join(opts)}</select>' + ''.join(panels) + '</div>')


def inline(t):
    spans = []
    def keep(m):
        spans.append(m.group(1)); return f'\x00{len(spans)-1}\x00'
    t = re.sub(r'`([^`]+)`', keep, t)
    t = html.escape(t, quote=False)
    t = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', r'<a href="\2">\1</a>', t)
    t = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', t)
    t = re.sub(r'(?<![\w*])\*([^*\n]+)\*(?![\w*])', r'<em>\1</em>', t)
    return re.sub(r'\x00(\d+)\x00',
                  lambda m: '<code>' + html.escape(spans[int(m.group(1))]) + '</code>', t)


def render(md):
    """Markdown subset -> HTML. Returns (body, h1 text)."""
    md = re.sub(r'^---\n.*?\n---\n', '', md, flags=re.S)        # front matter
    lines, out, i, title = md.split('\n'), [], 0, ''
    n = len(lines)
    while i < n:
        ln = lines[i]

        if ln.lstrip().startswith('<svg'):                       # inline figure
            buf = []
            while i < n:
                buf.append(lines[i])
                if '</svg>' in lines[i]: i += 1; break
                i += 1
            out.append('<figure class="flow">' + '\n'.join(buf) + '</figure>')
            continue

        if ln.strip() == '<!-- explorer: proofs -->':
            out.append(explorer()); i += 1; continue

        m = re.match(r'<!--\s*interactive:\s*(\S+)\s*-->', ln.strip())
        if m:
            out.append('<p class="snip-note">Hover or click any name below for its real type, '
                       "docstring or proof state &mdash; this is the Lean compiler's own data.</p>")
            src = m.group(1)
            f = HERE / src
            if f.exists():                       # a re-rendered snippet must not come from cache
                src += f'?v={int(f.stat().st_mtime)}'
            out.append(f'<div class="snipwrap"><iframe class="snip" loading="lazy" '
                       f'src="{src}" title="Interactive Lean snippet"></iframe></div>')
            i += 1; continue

        if ln.startswith('<!--'):
            i += 1; continue

        if ln.startswith('```'):
            lang = ln[3:].strip() or 'text'
            i += 1; buf = []
            while i < n and not lines[i].startswith('```'):
                buf.append(lines[i]); i += 1
            i += 1
            # A Lean block whose next line names a snippet is shown as that snippet
            # instead: same code, highlighted by Lean itself and hoverable.
            if lang == 'lean' and re.match(r'<!--\s*interactive:', lines[i].strip() if i < n else ''):
                continue
            cls = 'language-python' if lang == 'python' else ('lean-static' if lang == 'lean' else '')
            label = {'python': 'Python', 'lean': 'Lean 4'}.get(lang, '')
            lab = f'<span class="codelab">{label}</span>' if label else ''
            out.append(f'<div class="codeblock">{lab}<pre><code class="{cls}">'
                       f'{html.escape(chr(10).join(buf))}</code></pre></div>')
            continue

        m = re.match(r'^(#{1,3}) (.+)$', ln)
        if m:
            lvl, txt = len(m.group(1)), inline(m.group(2))
            if lvl == 1:
                title = txt
            else:
                out.append(f'<h{lvl}>{txt}</h{lvl}>')
            i += 1; continue

        if ln.startswith('|'):
            rows = []
            while i < n and lines[i].startswith('|'):
                rows.append(lines[i]); i += 1
            cells = [[c.strip() for c in r.strip().strip('|').split('|')] for r in rows]
            body = [r for r in cells if not re.match(r'^-+:?$|^:?-+:?$', r[0].replace(' ', ''))]
            th = ''.join(f'<th>{inline(c)}</th>' for c in body[0])
            tr = ''.join('<tr>' + ''.join(f'<td>{inline(c)}</td>' for c in r) + '</tr>'
                         for r in body[1:])
            out.append(f'<div class="tablewrap"><table><thead><tr>{th}</tr></thead>'
                       f'<tbody>{tr}</tbody></table></div>')
            continue

        if re.match(r'^(\d+\.|-) ', ln):
            ordered = bool(re.match(r'^\d+\.', ln))
            items = []
            while i < n and (re.match(r'^(\d+\.|-) ', lines[i]) or (lines[i].startswith('  ') and items)):
                if re.match(r'^(\d+\.|-) ', lines[i]):
                    items.append(re.sub(r'^(\d+\.|-) ', '', lines[i]))
                else:
                    items[-1] += ' ' + lines[i].strip()
                i += 1
            tag = 'ol' if ordered else 'ul'
            out.append(f'<{tag}>' + ''.join(f'<li>{inline(x)}</li>' for x in items) + f'</{tag}>')
            continue

        if ln.strip() == '---':
            out.append('<hr>'); i += 1; continue

        if not ln.strip():
            i += 1; continue

        buf = []
        while i < n and lines[i].strip() and not re.match(r'^(#{1,3} |```|\||<svg|<!--|---$|(\d+\.|-) )', lines[i]):
            buf.append(lines[i]); i += 1
        para = inline(' '.join(buf))
        cls = ' class="kicker"' if para.startswith('<em>PastaLean is open source') else ''
        out.append(f'<p{cls}>{para}</p>')

    return '\n'.join(out), title


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out')
    a = ap.parse_args()

    body, title = render(SRC.read_text())
    body = re.sub(r'<hr>\s*<p class="kicker">.*?</p>\s*$', '', body, flags=re.S)
    i = body.index('<h2>')
    body = body[:i] + NOTATION + '\n' + body[i:]

    head = (TPL / 'head.html').read_text()
    tail = (TPL / 'tail.html').read_text()
    page = MAST.format(title=title) + '\n' + body + '\n' + FOOT

    plain = re.sub(r'<[^>]+>', '', title)
    doc = ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
           '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
           f'<meta name="description" content="{html.escape(plain)}">\n'
           + head + '\n</head>\n<body>\n' + TOGGLE + '\n' + page + '\n' + tail
           + '\n</body>\n</html>\n')
    out = pathlib.Path(a.out) if a.out else HERE / 'index.html'

    out.write_text(doc)
    print(f'{out}  {len(doc)} bytes | iframes {doc.count(chr(34)+"snip"+chr(34))} '
          f'| tables {doc.count("<table>")} | static-lean {doc.count("lean-static")}')


if __name__ == '__main__':
    main()
