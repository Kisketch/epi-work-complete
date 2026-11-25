# -*- coding: utf-8 -*-
"""Paper 2 (2026-11-25): Add verified comparative benchmarks and missing DOIs.

Updates:
1. sec-preface.tex (+ intro-2C.tex / intro-2B.tex): cite Hensley (1996 + erratum 10.1006/jnth.1996.0107),
   Jenkinson--Pollicott (2018, 10.1016/j.aim.2017.11.028), and Chitanga--Lemmens--Nussbaum
   (2026, 10.1016/j.indag.2026.03.008 / arXiv:2504.20878v2).
2. sec-preface.tex (+ intro-2A.tex): cite Baker--Ward (2025, arXiv:2510.18451v1) and
   Tan--Tian--Wang--Wu (2026, arXiv:2511.02492v2, author Chen Tian).
3. sec-resasymp.tex & sec-num.tex: cite Chousionis--Leykekhman--Urbanski--Wendt (arXiv:2408.06330v2)
   and Brown (2026, arXiv:2604.20812v2) rigorous B-spline enclosure for E_{1,2}.
4. sec-verification.tex & refs.tex: fill DOIs for BV, CLU, FLLW, MW; strip \\allowbreak inside DOIs
   so automated extractors (verify_refs.py) parse DOIs reliably; add the 7 new \\bibitem entries.
5. Reconstruct paper2_spectral_gap_dimension.tex byte-for-byte from split/src_sections/slice_index.csv.
"""
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P2 = ROOT / "paper2_spectral_gap_dimension"
SL = P2 / "split" / "src_sections"
MAIN_TEX = P2 / "paper2_spectral_gap_dimension.tex"
SLICE_CSV = SL / "slice_index.csv"


def norm_crlf(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\n", "\r\n")


def replace_once(path: Path, old: str, new: str) -> None:
    raw = path.read_bytes().decode("utf-8")
    old_c = norm_crlf(old)
    new_c = norm_crlf(new)
    count = raw.count(old_c)
    assert count == 1, f"{path.name}: expected 1 match for snippet {old[:60]!r}, found {count}"
    path.write_bytes(raw.replace(old_c, new_c, 1).encode("utf-8"))


NEW_BIB_BODY = r"""\begin{thebibliography}{99}
\bibitem{BW2025} S.~Baker and B.~Ward, \emph{A quantitative framework for sets of
exact approximation order by rational numbers}, arXiv:2510.18451v1 (2025).

\bibitem{BDS} A.~B\'ir\'o, J.-M.~Deshouillers, V.~T.~S\'os, \emph{Good
approximation and characterization of subgroups of $\R/\Z$}, Studia Sci.\ Math.\ Hungar.\ 38 (2001), 97--113, doi:10.1556/sscmath.38.2001.1-4.7.

\bibitem{BV} V.~Beresnevich and S.~Velani, \emph{A mass transference principle
and the Duffin--Schaeffer conjecture}, Ann.\ of Math.\ (2) 164 (2006), no.~3, 971--992, doi:10.4007/annals.2006.164.971.

\bibitem{Brown2026} J.~Brown, \emph{Rigorous High-Order Hausdorff Dimension
Estimation of Limit Sets of Continued Fraction Iterated Function Systems via B-Splines},
arXiv:2604.20812v2 (2026).

\bibitem{BLR} Y.~Bugeaud, L.~Liao, M.~Rams, \emph{Metrical results on the
distribution of fractional parts of powers of real numbers}, Proc.\ Edinb.\ Math.\ Soc.\ (2) 62 (2019), 505--521, doi:10.1017/S0013091518000585; arXiv:1710.03596. (Cor.~8, the hypothesis is $Q_{j+1}/Q_j\to\infty$.)

\bibitem{CZ} W.~Cheng and X.~Zhang, \emph{Exact approximation order of real numbers in
Cantor series expansions}, arXiv:2606.30435v2 (2026).

\bibitem{CLN2026} P.~Chitanga, B.~Lemmens, R.~Nussbaum, \emph{On the structure of
the dimension spectrum for continued fraction expansions}, Indag.\ Math.\ 37 (2026),
no.~6, 1960--1989, doi:10.1016/j.indag.2026.03.008; arXiv:2504.20878v2.

\bibitem{CMMS} C.~Cabrelli, F.~Mendivil, U.~M.~Molter, R.~Shonkwiler,
\emph{On the Hausdorff $h$-measure of Cantor sets}, Pacific J.\ Math.\ 217
(2004), 45--59, doi:10.2140/pjm.2004.217.45.

\bibitem{CLU} V.~Chousionis, D.~Leykekhman, M.~Urba\'nski, \emph{On the
dimension spectrum of infinite subsystems of continued fractions}, Trans.\ Amer.\ Math.\ Soc.\ 373 (2020), no.~2, 1009--1042, doi:10.1090/tran/7984; arXiv:1805.11904.

\bibitem{CLUW2024} V.~Chousionis, D.~Leykekhman, M.~Urba\'nski, E.~Wendt,
\emph{Rigorous Hausdorff dimension estimates for conformal fractals},
arXiv:2408.06330v2 (2025).

\bibitem{Falconer} K.~Falconer, \emph{Fractal Geometry: Mathematical
Foundations and Applications}, 2nd ed., Wiley, 2003. (Countable sets have
Hausdorff dimension~$0$.)

\bibitem{FLLW} A.-H.~Fan, L.-M.~Liao, B.-W.~Wang, J.~Wu, \emph{On Khintchine
exponents and Lyapunov exponents of continued fractions}, Ergodic Theory Dynam.\ Systems 29 (2009), no.~1, 73--109, doi:10.1017/s0143385708000138.

\bibitem{FWW} D.-J.~Feng, Z.-Y.~Wen, J.~Wu, \emph{Some dimensional results
for homogeneous Moran sets}, Sci.\ China Ser.\ A 40 (1997), 475--482,
doi:10.1007/BF02896955.

\bibitem{Hensley1996} D.~Hensley, \emph{A Polynomial Time Algorithm for the
Hausdorff Dimension of Continued Fraction Cantor Sets}, J.\ Number Theory 58 (1996),
no.~1, 9--45, doi:10.1006/jnth.1996.0058; Erratum, J.\ Number Theory 59 (1996),
no.~2, 419, doi:10.1006/jnth.1996.0107.

\bibitem{JP2018} O.~Jenkinson and M.~Pollicott, \emph{Rigorous effective bounds
on the Hausdorff dimension of continued fraction Cantor sets: A hundred decimal digits
for the dimension of $E_2$}, Adv.\ Math.\ 325 (2018), 87--115,
doi:10.1016/j.aim.2017.11.028.

\bibitem{KL} C.~Kraaikamp and P.~Liardet, \emph{Good approximations and
continued fractions}, Proc.\ Amer.\ Math.\ Soc.\ 112 (1991), 303--309, doi:10.1090/s0002-9939-1991-1062392-7.

\bibitem{LimaMoreira} D.~Lima and C.~G.~Moreira, \emph{Phase transitions on
the Markov and Lagrange dynamical spectra}, Ann.\ Inst.\ H.~Poincar\'e
C Anal.\ Non Lin\'eaire 38 (2021), 1429--1459,
doi:10.1016/j.anihpc.2020.11.007; arXiv:1801.04636.

\bibitem{Moreira} C.~G.~Moreira, \emph{Geometric properties of the Markov and
Lagrange spectra}, Ann.\ of Math.\ (2) 188 (2018), 145--170,
doi:10.4007/annals.2018.188.1.3.

\bibitem{MEA} C.~G.~Moreira, H.~Erazo, N.~Angelini,
\emph{Generalized Hausdorff measure of irrationals with Lagrange value exactly 3},
arXiv:2511.10328v3.

{\sloppy
\bibitem{MW} R.~D.~Mauldin and S.~C.~Williams,
\emph{Hausdorff dimension in graph directed constructions},
Trans.~Amer.~Math.~Soc.~309 (1988), no.~2, 811--829, doi:10.1090/s0002-9947-1988-0961615-4.
}

\bibitem{Phase1} Phase-1 archive, \emph{On the irrationality of $e+\pi$}
(formalization project), Lean~4 modules \texttt{EpiFormal/\allowbreak Classification.lean}
(Theorem~2 and Corollary~3) and \texttt{EpiFormal/\allowbreak Spectral\allowbreak Gap.lean}, 2026-11-15.

\bibitem{TTWW2026} B.~Tan, C.~Tian, B.-W.~Wang, J.~Wu, \emph{Hausdorff measures of
sets in Exact Diophantine approximation}, arXiv:2511.02492v2 (2026).
\end{thebibliography}"""


def main():
    old_cf_prior = (
        "For the modular continued-fraction alphabets $F_{m,r}=\\{[0;a_1,a_2,\\dots]:a_n\\equiv r\\pmod m\\}$,\n"
        "infinite-alphabet thermodynamic-formalism dimension theory goes back to Hensley,\n"
        "Jenkinson--Pollicott, and Chousionis--Leykekhman--Urba\\'nski \\cite{CLU}; here"
    )
    new_cf_prior = (
        "For the modular continued-fraction alphabets $F_{m,r}=\\{[0;a_1,a_2,\\dots]:a_n\\equiv r\\pmod m\\}$,\n"
        "infinite-alphabet thermodynamic-formalism dimension theory goes back to Hensley \\cite{Hensley1996}\n"
        "(whose polynomial-time paper carries a published erratum), Jenkinson--Pollicott \\cite{JP2018},\n"
        "and Chousionis--Leykekhman--Urba\\'nski \\cite{CLU}, while Chitanga--Lemmens--Nussbaum \\cite{CLN2026}\n"
        "recently proved full dimension spectra $[0,\\dimH F_{m,r}]$ for single arithmetic progressions\n"
        "$F_{m,r}$ (not addressing our uniform Lipschitz invariance across $E_m$, global strict separation\n"
        "$\\dimH F_{m,m}<\\dimH F_{m,1}$, constants $C_r$, or multi-residue asymptotics); here"
    )
    replace_once(SL / "sec-preface.tex", old_cf_prior, new_cf_prior)
    replace_once(SL / "intro-2C.tex", old_cf_prior, new_cf_prior)

    replace_once(
        SL / "intro-2B.tex",
        "[2B-NEW-S24] On the continued-fraction side this continues the\n"
        "infinite-alphabet dimension theory of Hensley and Jenkinson--Pollicott for\n"
        "sets defined by digit constraints.",
        "[2B-NEW-S24] On the continued-fraction side this continues the\n"
        "infinite-alphabet dimension theory of Hensley \\cite{Hensley1996}\n"
        "(with its published erratum) and Jenkinson--Pollicott \\cite{JP2018} for\n"
        "sets defined by digit constraints.",
    )

    old_exact_prior = (
        "Related metric questions for Cantor series expansions, where the approximation\n"
        "is measured by the tail $x-\\omega_n(x)$ of the partial sums, were studied by\n"
        "Cheng and Zhang~\\cite{CZ}, who determine Hausdorff dimensions of the\n"
        "corresponding limsup sets; spectra and exact gauges are not considered there."
    )
    new_exact_prior = (
        "Related metric questions for Cantor series expansions, where the approximation\n"
        "is measured by the tail $x-\\omega_n(x)$ of the partial sums, were studied by\n"
        "Cheng and Zhang~\\cite{CZ}, who determine Hausdorff dimensions of the\n"
        "corresponding limsup sets, and recent exact-approximation frameworks by Baker\n"
        "and Ward~\\cite{BW2025} and Tan, Tian, Wang and Wu~\\cite{TTWW2026} establish\n"
        "quantitative criteria and infinite Hausdorff $f$-measures for exact\n"
        "approximation sets in regular spaces; discrete spectral gaps, signed-coset\n"
        "collapse, and exact recurrence gauges for non-autonomous super-exponential\n"
        "denominators $(Q_j)$ are not considered there."
    )
    replace_once(SL / "sec-preface.tex", old_exact_prior, new_exact_prior)
    replace_once(SL / "intro-2A.tex", old_exact_prior, new_exact_prior)

    replace_once(
        SL / "sec-resasymp.tex",
        "\\end{table}\n\n\\paragraph{Lean status of Section~\\ref{sec:windows-residues}.}",
        "\\end{table}\n\n"
        "For comparison with external rigorous finite-element and high-order B-spline bounds on\n"
        "finite-alphabet continued-fraction limit sets such as $E_{\\{1,2\\}}$\n"
        "($s_0(\\{1,2\\})\\approx0.531280506$), see \\cite{CLUW2024,CLN2026,Brown2026}.\n\n"
        "\\paragraph{Lean status of Section~\\ref{sec:windows-residues}.}",
    )

    replace_once(
        SL / "sec-num.tex",
        "($s_0\\approx0.705660908$) exhibit the predicted $\\Theta(m^{-2s_0})$ excess\n"
        "scaling up to $m=4096$.",
        "($s_0\\approx0.705660908$) exhibit the predicted $\\Theta(m^{-2s_0})$ excess\n"
        "scaling up to $m=4096$.\n"
        "As external rigorous benchmarks on the finite-alphabet endpoint $E_{\\{1,2\\}}$,\n"
        "piecewise-linear finite-element bounds for conformal fractals were developed by\n"
        "Chousionis, Leykekhman, Urba\\'nski and Wendt~\\cite{CLUW2024}, and the degree-$4$\n"
        "B-spline hidden-positivity enclosure of Brown~\\cite{Brown2026} certifies\n"
        "$\\dimH E_{\\{1,2\\}}\\in[0.531280506277203, 0.531280506277205]$ (also bracketed in\n"
        "\\cite[Table~1]{CLN2026}), agreeing with our non-rigorous $32$-digit Chebyshev\n"
        "collocation estimate $s_0(\\{1,2\\})\\approx0.531280506$ to all nine displayed decimal places.",
    )

    # Update bibliography in both sec-verification.tex and refs.tex cleanly
    bib_re = re.compile(r"\\begin\{thebibliography\}\{99\}.*?\\end\{thebibliography\}", re.DOTALL)
    new_bib_crlf = norm_crlf(NEW_BIB_BODY)

    sec_ver = (SL / "sec-verification.tex").read_bytes().decode("utf-8")
    refs_old = (SL / "refs.tex").read_bytes().decode("utf-8")
    m_ver = bib_re.search(sec_ver)
    m_ref = bib_re.search(refs_old)
    assert m_ver and m_ref
    assert m_ver.group(0) == m_ref.group(0), "sec-verification bib block and refs.tex diverged before patch!"

    (SL / "sec-verification.tex").write_bytes(
        (sec_ver[:m_ver.start()] + new_bib_crlf + sec_ver[m_ver.end():]).encode("utf-8")
    )
    (SL / "refs.tex").write_bytes((new_bib_crlf + "\r\n").encode("utf-8"))

    # Reassemble paper2_spectral_gap_dimension.tex from slice_index.csv
    with open(SLICE_CSV, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))
    joined = b"".join((SL / r["File"]).read_bytes() for r in rows)
    MAIN_TEX.write_bytes(joined)
    print(f"Patched Paper 2 slices and rewrote {MAIN_TEX.name} ({len(joined)} bytes).")


if __name__ == "__main__":
    main()
