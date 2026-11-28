#!/usr/bin/env python3
"""Static sanity checks for a LaTeX file (no TeX installation needed).

Usage:  python3 check_tex.py [paper_draft.tex]

Checks (comments stripped first; an unescaped % starts a comment):
  1. \\ref / \\eqref / \\autoref targets  <->  \\label definitions (missing targets, duplicate labels,
     unused labels as warnings);
  2. \\cite keys  <->  \\bibitem keys (missing keys; unused bibitems as warnings);
  3. \\begin{env} / \\end{env} pairing (stack-based, reports line numbers);
  4. balance of unescaped braces { }, of \\[ \\], of \\( \\), of \\left / \\right, and parity of
     inline $ (with $$ counted separately);
  5. lists PLACEHOLDER- markers and NEW-k markers (these live in comments, so the raw text is scanned).
Exit code 0 if no errors (warnings allowed), 1 otherwise. This is a heuristic checker, not a TeX parser.
"""
import re
import sys
from collections import Counter

path = sys.argv[1] if len(sys.argv) > 1 else "paper_draft.tex"
raw = open(path, encoding="utf-8").read()
raw_lines = raw.split("\n")


def strip_comment(line):
    out = []
    i = 0
    while i < len(line):
        c = line[i]
        if c == "\\" and i + 1 < len(line):
            out.append(line[i:i + 2])
            i += 2
            continue
        if c == "%":
            break
        out.append(c)
        i += 1
    return "".join(out)


lines = [strip_comment(l) for l in raw_lines]
text = "\n".join(lines)
errors, warnings = [], []


def lineno(pos):
    return text.count("\n", 0, pos) + 1


# --- verbatim-like environments are not used in the draft; \texttt{...} contents are kept as is.

# 1. labels and refs
labels = [(m.group(1), lineno(m.start())) for m in re.finditer(r"\\label\{([^}]*)\}", text)]
lab_count = Counter(l for l, _ in labels)
for l, n in labels:
    if lab_count[l] > 1:
        errors.append(f"duplicate label '{l}' (line {n})")
refs = []
for m in re.finditer(r"\\(?:ref|eqref|autoref|pageref)\{([^}]*)\}", text):
    for key in m.group(1).split(","):
        refs.append((key.strip(), lineno(m.start())))
labset = set(lab_count)
for r, n in refs:
    if r not in labset:
        errors.append(f"\\ref to undefined label '{r}' (line {n})")
refset = {r for r, _ in refs}
for l, n in labels:
    if l not in refset:
        warnings.append(f"label '{l}' (line {n}) is never referenced")

# 2. cites and bibitems
bibitems = [(m.group(1), lineno(m.start())) for m in re.finditer(r"\\bibitem(?:\[[^\]]*\])?\{([^}]*)\}", text)]
bib_count = Counter(b for b, _ in bibitems)
for b, n in bibitems:
    if bib_count[b] > 1:
        errors.append(f"duplicate bibitem '{b}' (line {n})")
cites = []
for m in re.finditer(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", text):
    for key in m.group(1).split(","):
        cites.append((key.strip(), lineno(m.start())))
for c, n in cites:
    if c not in bib_count:
        errors.append(f"\\cite of undefined key '{c}' (line {n})")
citeset = {c for c, _ in cites}
for b, n in bibitems:
    if b not in citeset:
        warnings.append(f"bibitem '{b}' (line {n}) is never cited")

# 3. environments
stack = []
for m in re.finditer(r"\\(begin|end)\{([^}]*)\}", text):
    kind, env, n = m.group(1), m.group(2), lineno(m.start())
    if kind == "begin":
        stack.append((env, n))
    else:
        if not stack:
            errors.append(f"\\end{{{env}}} without \\begin (line {n})")
        elif stack[-1][0] != env:
            errors.append(f"\\end{{{env}}} (line {n}) closes \\begin{{{stack[-1][0]}}} (line {stack[-1][1]})")
            stack.pop()
        else:
            stack.pop()
for env, n in stack:
    errors.append(f"unclosed \\begin{{{env}}} (line {n})")

# 4. delimiters
def count_unescaped(s, ch):
    return len(re.findall(r"(?<!\\)" + re.escape(ch), s))

depth = 0
for i, l in enumerate(lines, 1):
    # remove escaped braces and \{ \} pairs
    s = re.sub(r"\\[{}]", "", l)
    for c in s:
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth < 0:
                errors.append(f"unbalanced '}}' at line {i}")
                depth = 0
if depth != 0:
    errors.append(f"brace depth at end of file is {depth} (should be 0)")

nd = len(re.findall(r"\\\[", text)); nc = len(re.findall(r"\\\]", text))
if nd != nc:
    errors.append(f"\\[ count {nd} != \\] count {nc}")
po = len(re.findall(r"\\\(", text)); pc = len(re.findall(r"\\\)", text))
if po != pc:
    errors.append(f"\\( count {po} != \\) count {pc}")
lft = len(re.findall(r"\\left(?![a-zA-Z])", text)); rgt = len(re.findall(r"\\right(?![a-zA-Z])", text))
if lft != rgt:
    errors.append(f"\\left count {lft} != \\right count {rgt}")
t2 = re.sub(r"\\\$", "", text)
dd = t2.count("$$")
single = t2.replace("$$", "").count("$")
if dd % 2:
    errors.append(f"odd number of $$ ({dd})")
if single % 2:
    errors.append(f"odd number of inline $ ({single})")
# per-paragraph $ parity (helps locate a stray $)
for para_start, para in [(m.start(), m.group(0)) for m in re.finditer(r"(?s).+?(?:\n\s*\n|\Z)", t2)]:
    if para.replace("$$", "").count("$") % 2:
        warnings.append(f"odd inline $ count in paragraph starting at line {lineno(para_start)}")

# 5. markers (raw text, since they are in comments)
ph = [(i, l.strip()) for i, l in enumerate(raw_lines, 1) if "PLACEHOLDER-" in l]
new = [(i, l.strip()) for i, l in enumerate(raw_lines, 1) if re.search(r"NEW-\d", l)]

# report
words = len(re.findall(r"[A-Za-z]+", re.sub(r"\\[A-Za-z]+", " ", text)))
print(f"file: {path}")
print(f"labels: {len(labels)}, refs: {len(refs)}, bibitems: {len(bibitems)}, cites: {len(cites)}")
print(f"approx. words of text (macros removed): {words}")
print(f"PLACEHOLDER markers: {len(ph)}")
for i, l in ph:
    print(f"  line {i}: {l[:110]}")
print(f"NEW-k markers: {len(new)}")
for i, l in new:
    print(f"  line {i}: {l[:110]}")
for w in warnings:
    print("WARNING:", w)
for e in errors:
    print("ERROR:", e)
print("RESULT:", "OK" if not errors else f"{len(errors)} error(s)")
sys.exit(1 if errors else 0)
