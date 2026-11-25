r"""Derive the journal-facing ("pub") body slices of track 2A from the shared slices (2026-11-25).

The shared slices carry the full Lean audit trail (theorem titles "Layer~A in Lean", parenthetical
declaration lists, "Lean status" paragraphs). The main paper and the supplement keep that trail. For
the 2A journal version the trail moves to the supplement: this script writes

    sec-class-2Apub.tex, sec-spectrum-2Apub.tex, sec-finite-2Apub.tex,
    sec-weights-2Apub.tex, sec-gauge-core-2Apub.tex

next to the sources, without touching the sources. Only formalization remarks are removed; every
mathematical statement and proof step is kept. A few sentences that mix the two are rewritten by the
explicit, asserted replacements in BESPOKE. The script fails if any formalization vocabulary
survives.

Usage (from the repository root):  python paper2_spectral_gap_dimension/split/derive_2A_pub.py
"""
import re
from pathlib import Path

SL = Path(__file__).resolve().parent / "src_sections"
SOURCES = {
    "sec-class": "sec-class-2Apub",
    "sec-spectrum-2A": "sec-spectrum-2Apub",
    "sec-finite": "sec-finite-2Apub",
    "sec-weights": "sec-weights-2Apub",
    "sec-gauge-core": "sec-gauge-core-2Apub",
}

# ---------------------------------------------------------------- bespoke rewrites (asserted, count == 1)
BESPOKE = {
    "sec-class": [
        ("The two results of this section were first proved, and Lean-kernel-checked at\n"
         "Layer~A, in the Phase-1 project \\cite{Phase1}. Here Layer~A means that the\n"
         "audited declaration in Lean~4 depends only on Lean's three standard base axioms\n"
         "\\texttt{propext}, \\texttt{Classical.choice} and \\texttt{Quot.sound}. For\n"
         "completeness we give short self-contained proofs.",
         "The two results of this section were first obtained in \\cite{Phase1}. For\n"
         "completeness we give short self-contained proofs."),
        ("The last estimate is not in mathlib v4.35, and earlier drafts of the Phase-1\n"
         "formalization assumed it as an axiom. Both $\\delta_j\\to0$ and\n"
         "$|\\delta_j|<1/(2jQ_j)$ are now kernel-checked Lean theorems\n"
         "(\\texttt{deltaSel\\_tendsto\\_zero} and \\texttt{abs\\_deltaSel\\_lt}, proved via\n"
         "\\texttt{DeltaSign.lean}), derived from the Hermite--Pad\\'e integral\n"
         "representation",
         "The last estimate follows from the Hermite--Pad\\'e integral\n"
         "representation"),
    ],
    "sec-spectrum-2A": [
        ("we state it separately because it is the form used\n"
         "below and the form directly machine-checked in \\texttt{SpectralGap.lean}.",
         "we state it separately because it is the form used\nbelow."),
        # the 2A journal version has no numerical section; drop the pointer to it
        (" For $x=B\\pi$ ($B=1,\\dots,10$),\n"
         "$\\sqrt2$, the golden ratio and random reals, the values $j\\|Q_jx\\|$ for\n"
         "$j\\le60$ are large (Section~\\ref{sec:num}), but such finite data do not\n"
         "determine $\\Lam(x)$. By",
         " By"),
    ],
    "sec-finite": [
        ("The entire covering argument ---\n"
         "factorial growth of $Q_j$, uniform branching bound, surviving-center recursion,\n"
         "periodicity reduction, Hausdorff-content estimate, and the countable-union\n"
         "assembly --- is \\emph{machine-checked at Layer~A}\n"
         "(\\texttt{EpiFormal/DimHCore.lean} + \\texttt{EpiFormal/DimHFinite.lean}, base\n"
         "axioms only, no \\texttt{sorryAx}, and \\emph{no} continued-fraction axioms).\n"
         "The elementary proof below mirrors the formalization.",
         "The argument is an elementary covering: factorial growth of $Q_j$, a uniform\n"
         "branching bound, a recursion for the surviving centres, reduction to $[0,1]$ by\n"
         "periodicity, a Hausdorff-content estimate, and countable stability."),
        (", formalized in mathlib as\n"
         "\\texttt{FloorSemiring.tendsto\\_pow\\_div\\_factorial\\_atTop})",
         ")"),
    ],
    "sec-weights": [
        ("the point $x_0$ constructed\n"
         "in \\texttt{QuarterPointFinal.lean} (with constant digits $d_j\\equiv1$) satisfies\n"
         "$j\\|Q_jx_0\\|\\to1/4$ (\\texttt{QuarterPointFinal.\\allowbreak lambda\\_x0\\_eq\\_quarter}).",
         "the point $x_0$ obtained from the constant digits $d_j\\equiv1$ (as in the\n"
         "proof of Theorem~\\ref{thm:full-spectrum}) satisfies $j\\|Q_jx_0\\|\\to1/4$."),
        (" The combined witness is\n"
         "kernel-checked at Layer~A in \\texttt{EpiFormal/\\allowbreak UnweightedCorrection.lean}\n"
         "(\\texttt{UnweightedCorrection.\\allowbreak witness}) using only the three Lean\n"
         "base axioms.",
         ""),
        ("(formalized in \\texttt{WeightedPhase.\\allowbreak content\\_\\allowbreak core\\_\\allowbreak tendsto} via\n"
         "\\texttt{FloorSemiring.\\allowbreak tendsto\\_\\allowbreak pow\\_\\allowbreak div\\_\\allowbreak factorial\\_\\allowbreak atTop} and continuity of\n"
         "$u\\mapsto u^\\beta$ at $0$)",
         "(by continuity of $u\\mapsto u^\\beta$ at $0$)"),
    ],
}
# whole paragraphs to drop: (start text, text that must end the dropped span, inclusive)
DROP_SPANS = {
    "sec-weights": [("\nThe Lean formalization in \\texttt{EpiFormal/\\allowbreak WeightedExactDim.lean}",
                     "(\\texttt{one\\_le\\_hausdorffMeasure\\_cantorSet}).\n")],
}

PAREN_STARTS = ("(Lean", "(in Lean", "(\\texttt{")   # in these slices every \texttt is a Lean name
STOP_MARKERS = ("\n\\begin{", "\n\\section", "\n\\subsection", "\n\\paragraph{",
                "\nThe gauge $h_k$ is exact")
FORBIDDEN = re.compile(r"Lean|texttt|Layer~A|kernel|mathlib|sorryAx|axiom|EpiFormal|\.lean")


def drop_parentheticals(t):
    """Remove balanced parentheticals that start with '(Lean' or '(in Lean'."""
    while True:
        hits = [i for i in (t.find(s) for s in PAREN_STARTS) if i >= 0]
        if not hits:
            return t
        i = min(hits)
        depth, j = 0, i
        while True:
            c = t[j]
            depth += (c == "(") - (c == ")")
            j += 1
            if depth == 0:
                break
        line_start = t.rfind("\n", 0, i) + 1
        line_end = t.find("\n", j)
        before_blank = t[line_start:i].strip() == ""
        after_blank = t[j:line_end].strip() == ""
        if before_blank and after_blank:          # the parenthetical fills whole lines
            t = t[:line_start] + t[line_end + 1:]
        else:                                     # inline: also drop one preceding space
            k = i - 1 if i > 0 and t[i - 1] in " \n" else i
            t = t[:k] + t[j:]


def drop_lean_paragraphs(t):
    r"""Remove '\paragraph{Lean ...}' blocks up to the next structural marker (or end of file)."""
    while True:
        i = t.find("\\paragraph{Lean")
        if i < 0:
            return t
        stops = [s for s in (t.find(m, i + 1) for m in STOP_MARKERS) if s >= 0]
        stop = min(stops) + 1 if stops else len(t)
        t = t[:i] + t[stop:]


def main():
    for src, dst in SOURCES.items():
        t = (SL / f"{src}.tex").read_text(encoding="utf-8")
        for old, new in BESPOKE.get(src, []):
            assert t.count(old) == 1, (src, old[:70])
            t = t.replace(old, new)
        for start, end in DROP_SPANS.get(src, []):
            assert t.count(start) == 1, (src, start[:60])
            i = t.index(start)
            j = t.index(end, i) + len(end)
            t = t[:i] + "\n" + t[j:]
        n_title = t.count(", Layer~A in Lean]")
        t = t.replace(", Layer~A in Lean]", "]")
        t = drop_lean_paragraphs(t)
        t = drop_parentheticals(t)
        t = re.sub(r"\n{3,}", "\n\n", t)
        bad = [m.group(0) for m in FORBIDDEN.finditer(t)]
        assert not bad, (src, bad[:10])
        (SL / f"{dst}.tex").write_text(t, encoding="utf-8")
        print(f"{src:16s} -> {dst}.tex  titles cleaned: {n_title}  lines: {t.count(chr(10))}")
    write_refs()


def write_refs():
    """refs-2Apub.tex: the shared bibliography restricted to the keys cited by the 2A pub sources."""
    text = "".join((SL / f"{n}.tex").read_text(encoding="utf-8")
                   for n in ["frontmatter-2Apub", "intro-2Apub", *SOURCES.values()])
    cited = set()
    for grp in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", text):
        cited.update(k.strip() for k in grp.split(","))
    refs = (SL / "refs.tex").read_text(encoding="utf-8")
    head, body = refs.split("\\begin{thebibliography}{99}\n", 1)
    body, tail = body.rsplit("\\end{thebibliography}", 1)
    # split into entries; an entry may be wrapped in a "{\sloppy ... }" group
    entries = re.split(r"\n(?=\\bibitem\{|\{\\sloppy\n\\bibitem\{)", "\n" + body)
    kept, keys = [], []
    for e in entries:
        m = re.search(r"\\bibitem\{([^}]+)\}", e)
        if m and m.group(1) in cited:
            kept.append(e.strip("\n"))
            keys.append(m.group(1))
    missing = cited - set(keys)
    assert not missing, f"cited but not in refs.tex: {missing}"
    out = head + "\\begin{thebibliography}{99}\n" + "\n\n".join(kept) + "\n\\end{thebibliography}" + tail
    (SL / "refs-2Apub.tex").write_text(out, encoding="utf-8")
    print(f"refs-2Apub.tex: {len(keys)} entries ({', '.join(keys)})")


if __name__ == "__main__":
    main()
