r"""Paper 1: rigorous large-denominator exclusions (2026-11-24).  Classification: 有限排除.

Reads verification/exclusion_runs_20261124/*.jsonl (one file per machine; one JSON line per run of
verification/rational_exclusion_bound_20261124.py).  Runs with equal (constant, digits) on different
machines must agree exactly (asserted).  Proposition prop:denominator-bounds states only bounds
reproduced on at least two machines; larger single-machine runs are listed in the table and flagged.

Idempotent: the inserted subsection sits between "% BEGIN/END denominator-bounds (auto)" markers and
is regenerated on every run; bibitems and the introduction bullet are inserted once.
Bibliography: Johansson2017Arb and Bailey1988 (bibliographic fields from Crossref; the Bailey
statement is quoted from the article's abstract, full text not checked), OEISA058651 (page and
b-file opened; all 20000 terms re-verified by verification/oeis_a058651_crosscheck_20261124.py).
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEX = ROOT / "paper1_e_plus_pi" / "01_main_paper" / "paper1_e_plus_pi.tex"
RUNS = ROOT / "verification" / "exclusion_runs_20261124"
OEIS_LOG = ROOT / "verification" / "oeis_a058651_crosscheck_20261124.log"

NAMES = {"epi_sum": r"e+\pi", "epi_prod": r"e\pi", "epi_diff": r"\pi-e", "pi_over_e": r"\pi/e"}
ORDER = ("epi_sum", "epi_prod", "epi_diff", "pi_over_e")
BEGIN, END = "% BEGIN denominator-bounds (auto)\n", "% END denominator-bounds (auto)\n"


def load():
    runs = {}                                   # (const, digits) -> {machine: signature}
    recs = {}
    for f in sorted(RUNS.glob("*.jsonl")):
        for line in f.read_text().splitlines():
            if not line.strip():
                continue
            d = json.loads(line)
            key = (d["const"], d["digits"])
            sig = (d["min_denominator_digits"], d["cf_common_steps"], tuple(d["cf_prefix"]))
            runs.setdefault(key, {})[f.stem] = sig
            recs[key] = d
    for key, by_machine in runs.items():
        assert len(set(by_machine.values())) == 1, ("cross-machine mismatch", key, by_machine)
    return runs, recs


def tex_int(n):
    return f"{n:,}".replace(",", "{,}")


def oeis_digits():
    for line in OEIS_LOG.read_text().splitlines():
        if line.startswith("digits of q_19998"):
            return int(line.split("q_19998 =")[1].split(",")[0])
    raise AssertionError("OEIS log missing")


def build():
    runs, recs = load()
    assert "ALL 20000 B-FILE TERMS CONFIRMED" in OEIS_LOG.read_text()
    rows, verified = [], {}
    for c in ORDER:
        for (cc, D) in sorted(k for k in runs if k[0] == c):
            d, nm = recs[(cc, D)], len(runs[(cc, D)])
            if nm >= 2 and (c not in verified or D > verified[c]["digits"]):
                verified[c] = d
            rows.append(f"${NAMES[c]}$ & ${tex_int(D)}$ & $10^{{{tex_int(d['min_denominator_digits'] - 1)}}}$ & "
                        f"${tex_int(d['cf_common_steps'])}$ & {nm} \\\\")
    assert set(verified) == set(ORDER), verified
    bounds = {c: verified[c]["min_denominator_digits"] - 1 for c in ORDER}
    same = len(set(bounds.values())) == 1
    single = [(c, D) for (c, D), m in runs.items() if len(m) == 1]
    best_single = {}
    for c, D in single:
        if D > verified[c]["digits"] and (c not in best_single or D > best_single[c]["digits"]):
            best_single[c] = recs[(c, D)]
    single_txt = ""
    if best_single:
        parts = [f"$q\\ge10^{{{tex_int(best_single[c]['min_denominator_digits'] - 1)}}}$ for ${NAMES[c]}$ "
                 f"($D={tex_int(best_single[c]['digits'])}$)" for c in ORDER if c in best_single]
        single_txt = (r" Runs with larger $D$ on a single machine (last column $=1$) give " +
                      ", ".join(parts) + r"; they use the same code but have not been reproduced independently.")
    if same:
        prop = (r"If $x\in\{e+\pi,\ e\pi,\ \pi-e,\ \pi/e\}$ and $x=p/q$ with integers $p,q$ and $q\ge1$, then "
                r"$q\ge10^{" + tex_int(bounds["epi_sum"]) + r"}$.")
    else:
        prop = (r"If $x=p/q$ with integers $p,q$ and $q\ge1$, then $q\ge10^{K_x}$ with " +
                ", ".join(f"$K_{{{NAMES[c]}}}={tex_int(bounds[c])}$" for c in ORDER) + ".")
    D0 = verified["epi_sum"]["digits"]
    sub = BEGIN + r"""\subsection{Rigorous large-denominator exclusions}\label{sub:denominator-bounds}

Let $x$ be one of $e+\pi$, $e\pi$, $\pi-e$, $\pi/e$. Ball arithmetic
(Arb~\cite{Johansson2017Arb}, through python-flint) gives an interval $I=[\ell,u]$ with exact
dyadic endpoints and width below $10^{-D}$ that rigorously contains $x$. Let $h/k$ be the
rational number of least denominator in $I$; it is unique and is computed exactly from $\ell$
and $u$ by the continued-fraction algorithm for the simplest rational in a closed interval. If
$x=p/q$ with integers $p,q\ge1$, then $p/q\in I$, hence $q\ge k$.

\begin{proposition}[Finite exclusion of small denominators]\label{prop:denominator-bounds}
""" + prop + r"""
\end{proposition}

\begin{proof}[Computation]
Apply the argument above with $D=""" + tex_int(D0) + r"""$; the least denominators $k$ are listed in
Table~\ref{tab:denominator-bounds}. Each of these runs was carried out on two different machines
with identical results (least-denominator size, number of common partial quotients, and the
first $40$ partial quotients).
\end{proof}

\begin{table}[ht]
\centering\small
\begin{tabular}{c|c|c|c|c}
$x$ & digits $D$ & $q\ge$ & common CF terms & machines \\\hline
""" + "\n".join(rows) + r"""
\end{tabular}
\caption{If $x=p/q$ then $q$ is at least the stated power of $10$ (the least denominator $k$ in $I$ has one more decimal digit than the exponent). ``Common CF terms'' is the number of
partial quotients shared by both endpoints of $I$ (all of them are partial quotients of $x$);
``machines'' is the number of independent machines on which the run was reproduced with
identical output.}
\label{tab:denominator-bounds}
\end{table}

\noindent""" + single_txt + r""" The computation is reproducible with
\texttt{verification/\allowbreak rational\_\allowbreak exclusion\_\allowbreak bound\_\allowbreak 20261124.py};
its self-test recomputes the simplest rational with an independent exact implementation and the
continued-fraction prefix with \texttt{mpmath} at higher precision. These are \emph{finite}
exclusions: they say nothing about the irrationality of $x$, since rationals of larger
denominator are not excluded, and they do not lower the difficulty of
Problem~\ref{prob:main}. For comparison, the $20000$ partial quotients of $e+\pi$ tabulated in
OEIS~A058651~\cite{OEISA058651} (all of which agree with the partial quotients certified by an
enclosure with $D=25{,}000$) give a bound of the same kind, $q\ge q_{19998}\ge10^{""" + tex_int(oeis_digits() - 1) + r"""}$, and, according to the abstract
of~\cite{Bailey1988}, $e+\pi$ satisfies no algebraic equation of degree at most $8$ with
integer coefficients of Euclidean norm at most $10^{9}$.
""" + END
    return sub


def main():
    t = TEX.read_text(encoding="utf-8")
    sub = build()
    if BEGIN in t:
        i, j = t.index(BEGIN), t.index(END) + len(END)
        t = t[:i] + sub + t[j:]
    else:
        anchor = r"\begin{proposition}[Certified separation on a denominator range]\label{prop:farey-gap}"
        assert t.count(anchor) == 1 and "sub:denominator-bounds" not in t
        t = t.replace(anchor, sub + "\n" + anchor)
    if r"\bibitem{Johansson2017Arb}" not in t:
        bib_anchor = r"\bibitem{OEIS}"
        assert t.count(bib_anchor) == 1
        t = t.replace(bib_anchor,
                      r"\bibitem{Johansson2017Arb} F.~Johansson, \emph{Arb: efficient arbitrary-precision midpoint-radius interval arithmetic}, IEEE Trans.~Comput.~66 (2017), no.~8, 1281--1292, doi:10.1109/TC.2017.2690633." "\n"
                      r"\bibitem{Bailey1988} D.~H.~Bailey, \emph{Numerical results on the transcendence of constants involving $\pi$, $e$, and Euler's constant}, Math.~Comp.~50 (1988), no.~181, 275--281, doi:10.1090/S0025-5718-1988-0917835-1." "\n"
                      r"\bibitem{OEISA058651} OEIS Foundation, \emph{Sequence A058651: Continued fraction for $\pi+e$}, \url{https://oeis.org/A058651} (b-file with $20000$ terms)." "\n"
                      + bib_anchor)
    old105 = r"twelve symbolic verifications plus a separate cosine-integral check, and a 450-digit interval-arithmetic certificate."
    new105 = r"twelve symbolic verifications plus a separate cosine-integral check, a 450-digit interval-arithmetic certificate, and rigorous large-denominator exclusions (Proposition~\ref{prop:denominator-bounds})."
    if new105 not in t:
        assert t.count(old105) == 1
        t = t.replace(old105, new105)
    TEX.write_text(t, encoding="utf-8")
    print("patched", TEX.name)


if __name__ == "__main__":
    main()
