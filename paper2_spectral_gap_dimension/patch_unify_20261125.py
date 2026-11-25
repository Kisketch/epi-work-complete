# -*- coding: utf-8 -*-
"""Unify Paper 2 slices after merging origin/claude/clever-darwin-a5bbf9 into main (2026-11-25).

1. Resolves the two merge-conflict blocks in sec-preface.tex and intro-2C.tex by
   combining d87c0e3 external benchmark citations (Hensley1996 + erratum, JP2018,
   CLN2026, BW2025, TTWW2026) with b97ae55 novelty positioning (DFSU, MU96,
   Hensley92, Good41, HU02, DLMF).
2. Resyncs frontmatter.tex and intro-shared.tex so they remain verbatim substrings
   of sec-preface.tex.
3. Strips \\allowbreak inside DOIs in sec-verification.tex and refs.tex (keeping
   28/28 bibitems identical and wrapping long entries in {\\sloppy ...}).
4. Fixes the displayed typo m^{-\\varepsilon} -> m^{-1-\\varepsilon} in sec-resasymp.tex
   before `\\qquad \\varepsilon:=2s-1=\\frac{\\alpha}{m}`.
5. Updates slice_index.csv line/byte counts and reassembles
   paper2_spectral_gap_dimension.tex byte-for-byte from the 11 canonical slices.
"""
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P2 = ROOT / "paper2_spectral_gap_dimension"
SL = P2 / "split" / "src_sections"
MAIN_TEX = P2 / "paper2_spectral_gap_dimension.tex"
SLICE_CSV = SL / "slice_index.csv"

ORDER = [
    "sec-preface.tex",
    "sec-class.tex",
    "sec-spectrum.tex",
    "sec-finite.tex",
    "sec-weights.tex",
    "sec-gauge.tex",
    "sec-growing.tex",
    "sec-windows.tex",
    "sec-resasymp.tex",
    "sec-num.tex",
    "sec-verification.tex",
]


def to_crlf(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\n", "\r\n")


UNIFIED_RESIDUE_BODY = (
    "the underlying infinite-alphabet dimension theory is that of Mauldin and\n"
    "Urba\\'nski \\cite{MU96} (see \\cite[Theorem~2.3]{CLU}), Hensley \\cite{Hensley1996}\n"
    "(whose polynomial-time paper carries a published erratum), Jenkinson and\n"
    "Pollicott \\cite{JP2018}, and Chousionis, Leykekhman and Urba\\'nski \\cite{CLU},\n"
    "who proved that every arithmetic-progression alphabet has full dimension\n"
    "spectrum, while Chitanga, Lemmens and Nussbaum \\cite{CLN2026} recently settled\n"
    "full dimension spectra $[0,\\dimH F_{m,r}]$ for single arithmetic progressions\n"
    "(not addressing our uniform Lipschitz invariance across $E_m$, global strict\n"
    "separation $\\dimH F_{m,m}<\\dimH F_{m,1}$, constants $C_r$, or multi-residue\n"
    "asymptotics). Asymptotic expansions of the Hausdorff dimension when generators\n"
    "with small derivative are added to or removed from a conformal IFS were\n"
    "developed by Das, Fishman, Simmons and Urba\\'nski \\cite{DFSU}, who\n"
    "strengthened Hensley's expansion \\cite{Hensley92} for partial quotients $\\le N$\n"
    "and Good's estimates \\cite{Good41} for partial quotients $\\ge N$. The families\n"
    "$F_{m,S,B}$ fall within the scope of their perturbation theorem\n"
    "\\cite[Theorem~4.1]{DFSU} (fixed finite $S$, added generators $\\ge m-\\max B$);\n"
    "in their notation the leading constant is $1/\\bar c=\\sum_{n\\ge0}\\sum_{w\\in S^n}q(w)^{-1}=C_S$\n"
    "when $s_0(S)<1/2$. Arithmetic-progression alphabets are not treated in\n"
    "\\cite{DFSU}, and Theorems~\\ref{thm:residues-asymptotic}\n"
    "and~\\ref{thm:multi-residue-asymptotic} make the first terms explicit for them;\n"
    "the $\\log m/m^2$ coefficient has the same structure as Hensley's\n"
    "$72/\\pi^4=2(6/\\pi^2)^2$ (cf.\\ \\cite[(1.4)]{DFSU}). Part~(i) of\n"
    "Theorem~\\ref{thm:multi-residue-asymptotic} is the classical Bowen formula\n"
    "written as the abscissa of a Poincar\\'e series; our contribution there is a\n"
    "proof that avoids the pressure formalism, together with its formalization.\n"
    "The upper bound in part~(v), and hence the supercritical case of part~(ii),\n"
    "follow from the Heinemann--Urba\\'nski estimate \\cite{HU02} (in the form of\n"
    "\\cite[Theorem~2.4]{CLU}) combined with the Lyapunov bound\n"
    "\\cite[Proposition~2.6]{CLU}, and the case $S=\\emptyset$ of part~(ii) follows\n"
    "from Good's theorem by monotonicity. Part~(iii) is a quantitative form of the\n"
    "Laurent expansion of $\\zeta$ at $1$ \\cite[(25.2.4)]{DLMF}. A targeted negative\n"
    "search (arXiv, Crossref and web search; coverage recorded in the verification\n"
    "archive) found no prior appearance of $C_r$, of $\\psi_{\\mathrm{Fib}}$, or of the\n"
    "coefficient $\\frac12 d^2C_S(\\gamma C_S-C_S')$ as asymptotic dimension constants\n"
    "of residue-class digit sets; this does not exclude such an appearance.\n"
    "% Theorem/equation numbers cited for CLU and DFSU above are those of arXiv:1805.11904v1 and\n"
    "% arXiv:2007.10554v2; the numbering of the published versions has not been verified\n"
    "% (verification/paper2_novelty_review_20261125.md)."
)

CONFLICT_RE = re.compile(
    r"<<<<<<< HEAD\r?\n.*?=======\r?\n.*?\r?\n>>>>>>> [^\r\n]+",
    re.DOTALL,
)


def resolve_preface_and_intro() -> None:
    pre_path = SL / "sec-preface.tex"
    pre_txt = pre_path.read_bytes().decode("utf-8")
    matches = CONFLICT_RE.findall(pre_txt)
    assert len(matches) == 1, f"Expected 1 conflict block in sec-preface.tex, found {len(matches)}"
    pre_resolved = CONFLICT_RE.sub(lambda _m: to_crlf(UNIFIED_RESIDUE_BODY), pre_txt, count=1)
    assert "<<<<<<<" not in pre_resolved and ">>>>>>>" not in pre_resolved
    pre_path.write_bytes(pre_resolved.encode("utf-8"))

    # Regenerate verbatim sub-slices frontmatter.tex and intro-shared.tex
    doc_idx = pre_resolved.index("\\begin{document}")
    fm_txt = pre_resolved[doc_idx:]
    (SL / "frontmatter.tex").write_bytes(fm_txt.encode("utf-8"))

    intro_idx = pre_resolved.index("\\section{Introduction}")
    ins_txt = pre_resolved[intro_idx:]
    (SL / "intro-shared.tex").write_bytes(ins_txt.encode("utf-8"))

    # Resolve intro-2C.tex conflict
    i2c_path = SL / "intro-2C.tex"
    i2c_txt = i2c_path.read_bytes().decode("utf-8")
    matches_2c = CONFLICT_RE.findall(i2c_txt)
    assert len(matches_2c) == 1, f"Expected 1 conflict block in intro-2C.tex, found {len(matches_2c)}"
    i2c_resolved = CONFLICT_RE.sub(lambda _m: to_crlf(UNIFIED_RESIDUE_BODY + "\nIn"), i2c_txt, count=1)
    assert "<<<<<<<" not in i2c_resolved and ">>>>>>>" not in i2c_resolved
    i2c_path.write_bytes(i2c_resolved.encode("utf-8"))


def clean_bib_dois() -> None:
    doi_repls = [
        (
            "\\bibitem{DFSU} T.~Das, L.~Fishman, D.~Simmons, M.~Urba\\'nski, \\emph{Hausdorff\n"
            "dimensions of perturbations of a conformal iterated function system via\n"
            "thermodynamic formalism}, Selecta Math.\\ (N.S.) 29 (2023), no.~2, Paper No.~19,\n"
            "doi:10.1007/\\allowbreak s00029-022-00820-z; arXiv:2007.10554.",
            "{\\sloppy\n"
            "\\bibitem{DFSU} T.~Das, L.~Fishman, D.~Simmons, M.~Urba\\'nski, \\emph{Hausdorff\n"
            "dimensions of perturbations of a conformal iterated function system via\n"
            "thermodynamic formalism}, Selecta Math.\\ (N.S.) 29 (2023), no.~2, Paper No.~19,\n"
            "doi:10.1007/s00029-022-00820-z; arXiv:2007.10554.\n"
            "}",
        ),
        (
            "\\bibitem{Good41} I.~J.~Good, \\emph{The fractional dimensional theory of continued\n"
            "fractions}, Proc.\\ Cambridge Philos.\\ Soc.\\ 37 (1941), 199--228,\n"
            "doi:10.1017/\\allowbreak S030500410002171X.",
            "{\\sloppy\n"
            "\\bibitem{Good41} I.~J.~Good, \\emph{The fractional dimensional theory of continued\n"
            "fractions}, Proc.\\ Cambridge Philos.\\ Soc.\\ 37 (1941), 199--228,\n"
            "doi:10.1017/S030500410002171X.\n"
            "}",
        ),
        (
            "\\bibitem{HU02} S.~Heinemann and M.~Urba\\'nski, \\emph{Hausdorff dimension estimates\n"
            "for infinite conformal IFSs}, Nonlinearity 15 (2002), 727--734,\n"
            "doi:10.1088/\\allowbreak 0951-7715/\\allowbreak 15/\\allowbreak 3/\\allowbreak 312.",
            "{\\sloppy\n"
            "\\bibitem{HU02} S.~Heinemann and M.~Urba\\'nski, \\emph{Hausdorff dimension estimates\n"
            "for infinite conformal IFSs}, Nonlinearity 15 (2002), 727--734,\n"
            "doi:10.1088/0951-7715/15/3/312.\n"
            "}",
        ),
        (
            "\\bibitem{Hensley92} D.~Hensley, \\emph{Continued fraction Cantor sets, Hausdorff\n"
            "dimension, and functional analysis}, J.\\ Number Theory 40 (1992), 336--358,\n"
            "doi:10.1016/\\allowbreak 0022-314X(92)90006-B.",
            "{\\sloppy\n"
            "\\bibitem{Hensley92} D.~Hensley, \\emph{Continued fraction Cantor sets, Hausdorff\n"
            "dimension, and functional analysis}, J.\\ Number Theory 40 (1992), 336--358,\n"
            "doi:10.1016/0022-314X(92)90006-B.\n"
            "}",
        ),
        (
            "\\bibitem{MU96} R.~D.~Mauldin and M.~Urba\\'nski, \\emph{Dimensions and measures in\n"
            "infinite iterated function systems}, Proc.\\ London Math.\\ Soc.\\ (3) 73 (1996),\n"
            "105--154, doi:10.1112/\\allowbreak plms/\\allowbreak s3-73.1.105.",
            "{\\sloppy\n"
            "\\bibitem{MU96} R.~D.~Mauldin and M.~Urba\\'nski, \\emph{Dimensions and measures in\n"
            "infinite iterated function systems}, Proc.\\ London Math.\\ Soc.\\ (3) 73 (1996),\n"
            "105--154, doi:10.1112/plms/s3-73.1.105.\n"
            "}",
        ),
    ]
    for fname in ("refs.tex", "sec-verification.tex"):
        p = SL / fname
        txt = p.read_bytes().decode("utf-8")
        for old, new in doi_repls:
            old_c = to_crlf(old)
            new_c = to_crlf(new)
            assert txt.count(old_c) == 1, f"{fname}: missing {old[:30]}"
            txt = txt.replace(old_c, new_c, 1)
        assert not re.search(r"doi:[^\n]*\\allowbreak", txt), f"DOI allowbreak remains in {fname}"
        p.write_bytes(txt.encode("utf-8"))

    # Assert bibliography block in sec-verification.tex matches refs.tex
    bib_re = re.compile(r"\\begin\{thebibliography\}\{99\}.*?\\end\{thebibliography\}", re.DOTALL)
    m1 = bib_re.search((SL / "sec-verification.tex").read_bytes().decode("utf-8"))
    m2 = bib_re.search((SL / "refs.tex").read_bytes().decode("utf-8"))
    assert m1 and m2 and m1.group(0) == m2.group(0), "sec-verification bib block != refs.tex"


def fix_resasymp_typo() -> None:
    p = SL / "sec-resasymp.tex"
    txt = p.read_bytes().decode("utf-8")
    old = to_crlf("d\\,C_S(1+\\varepsilon)\\left(\\frac{1}{\\varepsilon}+\\gamma+O(\\varepsilon)+O(m^{-1})\\right)m^{-\\varepsilon}=1+O(m^{-1}),\\qquad \\varepsilon:=2s-1=\\frac{\\alpha}{m}.")
    new = to_crlf("d\\,C_S(1+\\varepsilon)\\left(\\frac{1}{\\varepsilon}+\\gamma+O(\\varepsilon)+O(m^{-1})\\right)m^{-1-\\varepsilon}=1+O(m^{-1}),\\qquad \\varepsilon:=2s-1=\\frac{\\alpha}{m}.")
    assert txt.count(old) == 1, f"Expected 1 occurrence of typo display in sec-resasymp.tex, found {txt.count(old)}"
    p.write_bytes(txt.replace(old, new, 1).encode("utf-8"))


def rebuild_slice_index_and_main() -> None:
    with open(SLICE_CSV, encoding="utf-8-sig") as f:
        old_rows = {r["File"]: r["Desc"] for r in csv.DictReader(f)}
    cur_line = 1
    parts: list[bytes] = []
    out_rows: list[list[str]] = []
    for fname in ORDER:
        raw = (SL / fname).read_bytes()
        nlines = raw.decode("utf-8").count("\n")
        start = cur_line
        end = cur_line + nlines - 1
        cur_line = end + 1
        parts.append(raw)
        out_rows.append([fname, str(start), str(end), str(nlines), str(len(raw)), old_rows[fname]])

    buf = ['"File","Start","End","Lines","Bytes","Desc"']
    for row in out_rows:
        buf.append(",".join('"' + x.replace('"', '""') + '"' for x in row))
    SLICE_CSV.write_bytes(to_crlf("\n".join(buf) + "\n").encode("utf-8"))

    joined = b"".join(parts)
    MAIN_TEX.write_bytes(joined)
    print(f"Reassembled {MAIN_TEX.name}: {cur_line - 1} lines, {len(joined)} bytes.")


def main() -> None:
    resolve_preface_and_intro()
    clean_bib_dois()
    fix_resasymp_typo()
    rebuild_slice_index_and_main()


if __name__ == "__main__":
    main()
