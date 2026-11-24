"""Patch paper 2 (main tex + split sources): comparison with Bugeaud--Liao--Rams [BLR] Theorem 7 /
Corollary 8 for the polynomial and growing-quotient subcritical dimension theorems, a related-work
citation (Cheng--Zhang, arXiv:2606.30435), and Crossref-verified DOIs for [KL] and [BDS].

Source of the BLR hypotheses: arXiv:1710.03596v1 (HTML, read verbatim), see
verification/paper2_novelty_review_20261123.md. Every anchor must occur exactly once in each file
that contains it, and at least once in the main tex.
Usage: python paper2_spectral_gap_dimension/patch_blr_remarks_20261123.py
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAIN = HERE / "paper2_spectral_gap_dimension.tex"
SPLIT = sorted((HERE / "split" / "src_sections").glob("*.tex"))

POLY_ANCHOR = (r"by Lemma~\ref{lem:poly-lattice}(iv), proving~(iii)." "\n" r"\end{proof}" "\n")
POLY_REMARK = POLY_ANCHOR + r"""
\begin{remark}[Comparison with Bugeaud--Liao--Rams]\label{rem:poly-BLR}
For $\alpha=0$ the dimension assertion in Theorem~\ref{thm:poly-phase-transition}(ii)
also follows from Corollary~8 of \cite{BLR}, since $Q_{j+1}/Q_j\to\infty$, by taking
constant centres $y_j=t$ exactly as for the convergent denominators of~$e$.
For $0<\alpha<r$, the right-hand side of the dimension formula in
\cite[Theorem~7]{BLR}, evaluated formally at $f_j(x)=Q_jx$ and $\delta_j=t_0j^{-\alpha}$,
is $\liminf_n(\log Q_n+\sum_{j<n}\log\delta_j)/(\log Q_n-\log\delta_n)=1-\alpha/r$,
the value in~(ii). That theorem does not apply, however: its condition~(1.6) requires
$\log f'_{j+1}/\log f'_j\to\infty$, whereas here $\log Q_{j+1}/\log Q_j\to1$, and the
proof above does not use that condition. (Hypotheses as stated in arXiv:1710.03596v1.)
\end{remark}
"""

GROW_ANCHOR = (r"to $(\tau-1)\gamma_{\sup}-1$." "\n" r"\end{proof}" "\n")
GROW_REMARK = GROW_ANCHOR + r"""
\begin{remark}[Comparison with Bugeaud--Liao--Rams]\label{rem:growing-BLR}
Part~(i) of Theorem~\ref{thm:growing-rec-dim-phase} overlaps with \cite{BLR} in two
boundary regimes. For $\tau=0$, since $Q_{j+1}/Q_j\ge A_j\to\infty$, Corollary~8 of
\cite{BLR} already gives $\dimH E_{G,0,\mathrm{lim}}(0)=1$, hence also
$\dimH E_{G,0}(t)=1$. For $\tau>0$ and $\lim_{j\to\infty}\log A_j/\log Q_j=\infty$
(a limit, not only a $\limsup$), one has $\log Q_{j+1}/\log Q_j\to\infty$ because
$Q_{j+1}\ge A_jQ_j$; then, for $N$ large, the maps $x\mapsto Q_{j+N}x$ with
$\delta_j=(t+1)A_{j+N}^{-\tau}$ satisfy conditions~(1.1), (1.5) and~(1.6) of
\cite[Theorem~7]{BLR}, its dimension formula gives $0$, and
$E_{G,\tau}(t)\subseteq\bigcup_N\{x:\|Q_jx\|\le(t+1)A_j^{-\tau}\ \forall j\ge N\}$
yields $\dimH E_{G,\tau}(t)=0$ by countable stability. In all other cases---in
particular whenever $\gamma_{\sup}<\infty$, where $\log Q_{j+1}/\log Q_j$ stays
bounded---condition~(1.6) fails and \cite[Theorem~7]{BLR} does not apply. Its
right-hand side, evaluated formally at $f_j(x)=Q_jx$ and $\delta_j=cA_j^{-\tau}$, is
nevertheless $(1-\tau)/(1+\tau\gamma_{\sup})$ (using $\log Q_n=\sum_{j<n}\log A_j+O(n)$
and $n=o(\log Q_n)$), so~\eqref{eq:growing-subcritical-dim} may be read as an extension
of that formula beyond condition~(1.6). (Hypotheses as stated in arXiv:1710.03596v1.)
\end{remark}
"""

INTRO_ANCHOR = (r"For the selected sequence $(Q_j)$, Corollary~8 of Bugeaud, Liao and Rams" "\n"
                r"\cite{BLR} applies directly since $Q_{j+1}/Q_j\to\infty$.")
INTRO_NEW = (r"Related metric questions for Cantor series expansions, where the approximation" "\n"
             r"is measured by the tail $x-\omega_n(x)$ of the partial sums, were studied by" "\n"
             r"Cheng and Zhang~\cite{CZ}, who determine Hausdorff dimensions of the" "\n"
             r"corresponding limsup sets; spectra and exact gauges are not considered there." "\n"
             + INTRO_ANCHOR + r" Theorems~\ref{thm:poly-phase-transition} and" "\n"
             r"\ref{thm:growing-rec-dim-phase} are compared with \cite{BLR} in" "\n"
             r"Remarks~\ref{rem:poly-BLR} and~\ref{rem:growing-BLR}.")

BIB_EDITS = [
    (r"approximation and characterization of subgroups of $\R/\Z$}, Studia Sci.\ Math.\ Hungar.\ 38 (2001), 97--113.",
     r"approximation and characterization of subgroups of $\R/\Z$}, Studia Sci.\ Math.\ Hungar.\ 38 (2001), 97--113, doi:10.1556/\allowbreak sscmath.38.2001.1-4.7."),
    (r"continued fractions}, Proc.\ Amer.\ Math.\ Soc.\ 112 (1991), 303--309.",
     r"continued fractions}, Proc.\ Amer.\ Math.\ Soc.\ 112 (1991), 303--309, doi:10.1090/\allowbreak s0002-9939-1991-1062392-7."),
    (r"\bibitem{CMMS}",
     r"\bibitem{CZ} W.~Cheng and X.~Zhang, \emph{Exact approximation order of real numbers in" "\n"
     r"Cantor series expansions}, arXiv:2606.30435v2 (2026)." "\n\n" r"\bibitem{CMMS}"),
]


def apply(text, old, new, required):
    n = text.count(old)
    if n == 0:
        assert not required, f"anchor missing in main tex: {old[:70]!r}"
        return text, False
    assert n == 1, (n, old[:70])
    return text.replace(old, new), True


def main():
    files = [MAIN] + SPLIT
    for f in files:
        t = f.read_text(encoding="utf-8")
        orig = t
        for old, new in [(POLY_ANCHOR, POLY_REMARK), (GROW_ANCHOR, GROW_REMARK),
                         (INTRO_ANCHOR, INTRO_NEW)] + BIB_EDITS:
            t, _ = apply(t, old, new, required=(f == MAIN))
        if t != orig:
            f.write_text(t, encoding="utf-8")
            print("patched", f.relative_to(HERE))


def drop_2A_cross_ref():
    """2A track omits the polynomial/growing sections: drop the cross-reference sentence there."""
    f = HERE / "split" / "src_sections" / "intro-2A.tex"
    t = f.read_text(encoding="utf-8")
    s = (r" Theorems~\ref{thm:poly-phase-transition} and" "\n"
         r"\ref{thm:growing-rec-dim-phase} are compared with \cite{BLR} in" "\n"
         r"Remarks~\ref{rem:poly-BLR} and~\ref{rem:growing-BLR}.")
    if s in t:
        f.write_text(t.replace(s, ""), encoding="utf-8")
        print("patched", f.relative_to(HERE), "(2A cross-ref dropped)")


if __name__ == "__main__":
    main()
    drop_2A_cross_ref()
