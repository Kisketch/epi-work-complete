r"""Paper 2 (2026-11-25): apply the novelty wording of verification/paper2_novelty_review_20261125.md §5.

1. Replaces the residue paragraph of the prior-work section (Section sec:prior) with the §5.4 text:
   DFSU perturbation theory, the classical Bowen formula, Heinemann--Urbanski, Good, and the DLMF
   Laurent expansion are credited. The unsupported "Hensley, Jenkinson--Pollicott" attribution,
   which had no citations, is removed.
2. Rewords "Bowen-free Poincare-abscissa dimension" as a self-contained proof of a classical identity
   (abstract, introduction, Lean-status paragraph, verification section).
3. Splits the "main new contributions" lists (prior-work section and honesty statement): the residue
   large-m expansions become "explicit residue-class instances of known asymptotic methods".
4. Adds bibitems DFSU, DLMF, Good41, HU02, Hensley92, MU96. Fields are taken from Crossref and
   arXiv, as recorded in the review's §2. Theorem numbers cited for CLU and DFSU are arXiv-version
   numbers; the published numbering is not verified (a LaTeX comment marks this).

The shared slices are patched in step: the 13 core slices plus the verbatim sub-slices
frontmatter.tex, intro-shared.tex and refs.tex. The 2C derived intro (intro-2C.tex) gets the same
paragraph and wording. The script asserts that the 13 core slices concatenate byte-for-byte to the
main file before and after patching, and that the sub-slices remain verbatim substrings.

NOTE: split/intro_trim_2A.py, intro_trim_2B.py and intro_trim_2C.py derive the track intros from
intro-shared.tex by line number. This patch changes the line count of intro-shared.tex after the
prior-work paragraph, so do NOT re-run those scripts without updating their line tables. The
derived intro-2C.tex is patched directly here; intro-2A/2B do not contain the edited passages.
"""
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"
SL = ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections"
ORDER = ["sec-preface", "sec-class", "sec-spectrum", "sec-finite", "sec-weights", "sec-gauge-core",
         "sec-finstate", "sec-poly", "sec-growing", "sec-windows", "sec-resasymp", "sec-num",
         "sec-verification"]
SUB = {"frontmatter": "sec-preface", "intro-shared": "sec-preface", "refs": "sec-verification"}

# ---------------------------------------------------------------- shared replacements
PRIOR_START = r"For the modular continued-fraction alphabets $F_{m,r}="
PRIOR_END_MAIN = "rate of Theorem~\\ref{thm:multi-residue-asymptotic}).\n"

NEW_PRIOR = r"""For the modular continued-fraction alphabets $F_{m,r}=\{[0;a_1,a_2,\dots]:a_n\equiv r\pmod m\}$,
the underlying infinite-alphabet dimension theory is that of Mauldin and
Urba\'nski \cite{MU96} (see \cite[Theorem~2.3]{CLU}), and Chousionis, Leykekhman
and Urba\'nski \cite{CLU} proved that every arithmetic-progression alphabet has
full dimension spectrum. Asymptotic expansions of the Hausdorff dimension when
generators with small derivative are added to or removed from a conformal IFS
were developed by Das, Fishman, Simmons and Urba\'nski \cite{DFSU}, who
strengthened Hensley's expansion \cite{Hensley92} for partial quotients $\le N$
and Good's estimates \cite{Good41} for partial quotients $\ge N$. The families
$F_{m,S,B}$ fall within the scope of their perturbation theorem
\cite[Theorem~4.1]{DFSU} (fixed finite $S$, added generators $\ge m-\max B$);
in their notation the leading constant is $1/\bar c=\sum_{n\ge0}\sum_{w\in S^n}q(w)^{-1}=C_S$
when $s_0(S)<1/2$. Arithmetic-progression alphabets are not treated in
\cite{DFSU}, and Theorems~\ref{thm:residues-asymptotic}
and~\ref{thm:multi-residue-asymptotic} make the first terms explicit for them;
the $\log m/m^2$ coefficient has the same structure as Hensley's
$72/\pi^4=2(6/\pi^2)^2$ (cf.\ \cite[(1.4)]{DFSU}). Part~(i) of
Theorem~\ref{thm:multi-residue-asymptotic} is the classical Bowen formula
written as the abscissa of a Poincar\'e series; our contribution there is a
proof that avoids the pressure formalism, together with its formalization.
The upper bound in part~(v), and hence the supercritical case of part~(ii),
follow from the Heinemann--Urba\'nski estimate \cite{HU02} (in the form of
\cite[Theorem~2.4]{CLU}) combined with the Lyapunov bound
\cite[Proposition~2.6]{CLU}, and the case $S=\emptyset$ of part~(ii) follows
from Good's theorem by monotonicity. Part~(iii) is a quantitative form of the
Laurent expansion of $\zeta$ at $1$ \cite[(25.2.4)]{DLMF}. A targeted negative
search (arXiv, Crossref and web search; coverage recorded in the verification
archive) found no prior appearance of $C_r$, of $\psi_{\mathrm{Fib}}$, or of the
coefficient $\frac12 d^2C_S(\gamma C_S-C_S')$ as asymptotic dimension constants
of residue-class digit sets; this does not exclude such an appearance.
% Theorem/equation numbers cited for CLU and DFSU above are those of arXiv:1805.11904v1 and
% arXiv:2007.10554v2; the numbering of the published versions has not been verified
% (verification/paper2_novelty_review_20261125.md).
"""

SHARED = [
    # abstract (frontmatter / sec-preface)
    ("Theorem~\\ref{thm:multi-residue-asymptotic}\n"
     "establishes the Bowen-free Poincar\\'e-abscissa dimension $\\dimH E_S=s_0(S)$, the\n"
     "universal phase transition $\\dimH F_{m,S,B}\\to\\max(1/2,s_0(S))$, a three-term\n",
     "Theorem~\\ref{thm:multi-residue-asymptotic}\n"
     "gives a self-contained, Bowen-free proof of the classical identity\n"
     "$\\dimH E_S=s_0(S)$ and establishes the universal phase transition\n"
     "$\\dimH F_{m,S,B}\\to\\max(1/2,s_0(S))$, a three-term\n"),
    # introduction list (intro-shared / sec-preface)
    ("Bowen-free Poincar\\'e-abscissa dimension formula for finite alphabets $E_S$,\n",
     "self-contained Bowen-free proof of the classical Poincar\\'e-abscissa dimension\n"
     "formula for finite alphabets $E_S$,\n"),
    # main-new-contributions list in Section sec:prior
    ("and the continued-fraction window and\n"
     "residue theorems (Theorems~\\ref{thm:windows}--\\ref{thm:multi-residue-asymptotic}).\n",
     "the continued-fraction window and\n"
     "residue theorems (Theorems~\\ref{thm:windows}--\\ref{thm:residues-general} and the\n"
     "strict separation in Theorem~\\ref{thm:residues-asymptotic}(ii)), and explicit\n"
     "residue-class instances of known asymptotic methods\n"
     "(Theorems~\\ref{thm:residues-asymptotic}(iii)--(iv)\n"
     "and~\\ref{thm:multi-residue-asymptotic}).\n"),
    # Lean-status paragraph (sec-resasymp)
    ("(Bowen-free Poincar\\'e-abscissa dimension, multi-residue phase transition",
     "(Bowen-free proof of the Poincar\\'e-abscissa dimension formula, multi-residue phase transition"),
    # verification section: formalized-content list
    ("(Bowen-free Poincar\\'e-abscissa dimension for finite alphabets, universal\n",
     "(Bowen-free proof of the classical Poincar\\'e-abscissa dimension formula for\n"
     "finite alphabets, universal\n"),
    # verification section: honesty-statement contributions list
    (", and the\n"
     "window and residue theorems (Theorems~\\ref{thm:windows}--\\ref{thm:multi-residue-asymptotic}).\n",
     ", the\n"
     "window and residue theorems (Theorems~\\ref{thm:windows}--\\ref{thm:residues-general}\n"
     "and Theorem~\\ref{thm:residues-asymptotic}(ii)), and explicit residue-class\n"
     "instances of known asymptotic methods\n"
     "(Theorems~\\ref{thm:residues-asymptotic}(iii)--(iv)\n"
     "and~\\ref{thm:multi-residue-asymptotic}; see Section~\\ref{sec:prior}).\n"),
    # bibliography
    ("Trans.\\ Amer.\\ Math.\\ Soc.\\ 373 (2020), 1009--1042, arXiv:1805.11904.\n\n",
     "Trans.\\ Amer.\\ Math.\\ Soc.\\ 373 (2020), 1009--1042, arXiv:1805.11904.\n\n"
     "\\bibitem{DFSU} T.~Das, L.~Fishman, D.~Simmons, M.~Urba\\'nski, \\emph{Hausdorff\n"
     "dimensions of perturbations of a conformal iterated function system via\n"
     "thermodynamic formalism}, Selecta Math.\\ (N.S.) 29 (2023), no.~2, Paper No.~19,\n"
     "doi:10.1007/\\allowbreak s00029-022-00820-z; arXiv:2007.10554.\n\n"
     "\\bibitem{DLMF} \\emph{NIST Digital Library of Mathematical Functions}, \\S25.2,\n"
     "Release~1.2.8 of 2026-09-15, \\url{https://dlmf.nist.gov/25.2}.\n\n"),
    ("doi:10.1007/\\allowbreak BF02896955.\n\n",
     "doi:10.1007/\\allowbreak BF02896955.\n\n"
     "\\bibitem{Good41} I.~J.~Good, \\emph{The fractional dimensional theory of continued\n"
     "fractions}, Proc.\\ Cambridge Philos.\\ Soc.\\ 37 (1941), 199--228,\n"
     "doi:10.1017/\\allowbreak S030500410002171X.\n\n"
     "\\bibitem{HU02} S.~Heinemann and M.~Urba\\'nski, \\emph{Hausdorff dimension estimates\n"
     "for infinite conformal IFSs}, Nonlinearity 15 (2002), 727--734,\n"
     "doi:10.1088/\\allowbreak 0951-7715/\\allowbreak 15/\\allowbreak 3/\\allowbreak 312.\n\n"
     "\\bibitem{Hensley92} D.~Hensley, \\emph{Continued fraction Cantor sets, Hausdorff\n"
     "dimension, and functional analysis}, J.\\ Number Theory 40 (1992), 336--358,\n"
     "doi:10.1016/\\allowbreak 0022-314X(92)90006-B.\n\n"),
    ("arXiv:2511.10328v3.\n\n{\\sloppy\n\\bibitem{MW}",
     "arXiv:2511.10328v3.\n\n"
     "\\bibitem{MU96} R.~D.~Mauldin and M.~Urba\\'nski, \\emph{Dimensions and measures in\n"
     "infinite iterated function systems}, Proc.\\ London Math.\\ Soc.\\ (3) 73 (1996),\n"
     "105--154, doi:10.1112/\\allowbreak plms/\\allowbreak s3-73.1.105.\n\n"
     "{\\sloppy\n\\bibitem{MW}"),
]

# ---------------------------------------------------------------- 2C-only replacements
PRIOR_END_2C = "asymptotic dimension constant of modular continued-fraction digit sets). In\n"
TWO_C = [
    ("giving a Bowen-free Poincar\\'e-abscissa\ndimension formula for $E_S$,",
     "giving a self-contained Bowen-free proof\nof the classical Poincar\\'e-abscissa dimension formula for $E_S$,"),
    ("giving a\nBowen-free Poincar\\'e-abscissa formula $\\dimH E_S=s_0(S)$,",
     "giving a\nself-contained Bowen-free proof of the classical Poincar\\'e-abscissa formula\n$\\dimH E_S=s_0(S)$,"),
    ("the residue dimensions, phase transition, and asymptotics (Theorems~\\ref{thm:residues},\n"
     "~\\ref{thm:residues-general}, \\ref{thm:residues-asymptotic}, and~\\ref{thm:multi-residue-asymptotic} with\n"
     "Tables~\\ref{tab:residues-general}, \\ref{tab:residues-asymptotic}, and~\\ref{tab:multi-residue-asymptotic}), and\n",
     "the residue dimensions and strict separation (Theorems~\\ref{thm:residues},\n"
     "\\ref{thm:residues-general}, and~\\ref{thm:residues-asymptotic}(ii), with\n"
     "Table~\\ref{tab:residues-general}), explicit residue-class instances of known\n"
     "asymptotic methods (Theorems~\\ref{thm:residues-asymptotic}(iii)--(iv)\n"
     "and~\\ref{thm:multi-residue-asymptotic}, with Tables~\\ref{tab:residues-asymptotic}\n"
     "and~\\ref{tab:multi-residue-asymptotic}), and\n"),
]


def replace_prior(text, end_marker, tail):
    """Replace the residue paragraph from PRIOR_START up to end_marker by NEW_PRIOR + tail."""
    if PRIOR_START not in text:
        return text, 0
    assert text.count(PRIOR_START) == 1
    i = text.index(PRIOR_START)
    j = text.index(end_marker, i) + len(end_marker)
    return text[:i] + NEW_PRIOR + tail + text[j:], 1


def main():
    rd = lambda p: p.read_bytes().decode("utf-8")
    main_t = rd(TEX)
    core = {n: rd(SL / f"{n}.tex") for n in ORDER}
    sub = {n: rd(SL / f"{n}.tex") for n in SUB}
    intro2c = rd(SL / "intro-2C.tex")
    assert "".join(core[n] for n in ORDER) == main_t, "core slices out of sync before patch"
    for n, parent in SUB.items():
        assert sub[n] in core[parent], f"{n} not a substring of {parent} before patch"
    assert "bibitem{DFSU}" not in main_t, "already patched"

    # prior-work paragraph
    main_t, k = replace_prior(main_t, PRIOR_END_MAIN, "")
    assert k == 1
    hits = 0
    for n in ORDER:
        core[n], k = replace_prior(core[n], PRIOR_END_MAIN, "")
        hits += k
    assert hits == 1
    for n in SUB:
        sub[n], _ = replace_prior(sub[n], PRIOR_END_MAIN, "")
    intro2c, k = replace_prior(intro2c, PRIOR_END_2C, "In\n")
    assert k == 1

    # shared replacements
    for old, new in SHARED:
        assert main_t.count(old) == 1, ("main", old[:60])
        main_t = main_t.replace(old, new)
        n_core = sum(core[n].count(old) for n in ORDER)
        assert n_core == 1, ("core", old[:60], n_core)
        for n in ORDER:
            core[n] = core[n].replace(old, new)
        for n in SUB:
            sub[n] = sub[n].replace(old, new)

    # 2C-only replacements
    for old, new in TWO_C:
        assert intro2c.count(old) == 1, ("intro-2C", old[:60])
        intro2c = intro2c.replace(old, new)

    assert "".join(core[n] for n in ORDER) == main_t, "core slices out of sync after patch"
    for n, parent in SUB.items():
        assert sub[n] in core[parent], f"{n} not a substring of {parent} after patch"
    for key in ("DFSU", "DLMF", "Good41", "HU02", "Hensley92", "MU96"):
        assert main_t.count("\\bibitem{%s}" % key) == 1
        assert "{%s}" % key in sub["refs"]
    assert "Hensley,\nJenkinson--Pollicott" not in main_t and "Hensley,\nJenkinson--Pollicott" not in intro2c

    TEX.write_bytes(main_t.encode("utf-8"))
    for n in ORDER:
        (SL / f"{n}.tex").write_bytes(core[n].encode("utf-8"))
    for n in SUB:
        (SL / f"{n}.tex").write_bytes(sub[n].encode("utf-8"))
    (SL / "intro-2C.tex").write_bytes(intro2c.encode("utf-8"))
    print("patched; main sha256", hashlib.sha256(main_t.encode("utf-8")).hexdigest(),
          "| lines", main_t.count("\n"), "| bytes", len(main_t.encode("utf-8")))


if __name__ == "__main__":
    main()
