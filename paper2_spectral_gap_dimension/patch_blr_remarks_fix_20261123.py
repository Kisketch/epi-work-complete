"""Paper 2: apply the adversarial-review fixes to rem:poly-BLR / rem:growing-BLR (2026-11-23).

Review findings (no mathematical error found): restore the antecedent of "It" in the
introduction; local-vs-global dimension wording; restrict to 0<tau<1; avoid the letter c
(poly leading coefficient) and undefined A_j (j<J_0) / j^{-alpha} at j=0; note that BLR
Corollary 8 is stated without proof in v1 and that BLR's sketch indicates (1.6) may be
removable (Baker's interpolation), not stated as a theorem; record E_lim(0) in E(t).
Every anchor must match exactly once in each file containing it, and at least once overall.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
FILES = [HERE / "paper2_spectral_gap_dimension.tex"] + sorted((HERE / "split" / "src_sections").glob("*.tex"))

BAKER = (r"(Hypotheses as stated in arXiv:1710.03596v1, whose proof sketch indicates that" "\n"
         r"condition~(1.6) may be removable by an interpolation device of Baker; this is not" "\n"
         r"stated there as a theorem.)")

EDITS = [
    (r"Remarks~\ref{rem:poly-BLR} and~\ref{rem:growing-BLR}. It gives dimension",
     r"Remarks~\ref{rem:poly-BLR} and~\ref{rem:growing-BLR}. Corollary~8 gives dimension"),
    # rem:poly-BLR
    (r"also follows from Corollary~8 of \cite{BLR}, since $Q_{j+1}/Q_j\to\infty$, by taking",
     r"also follows from Corollary~8 of \cite{BLR} (stated there without proof), since" "\n"
     r"$Q_{j+1}/Q_j\to\infty$, by taking"),
    (r"evaluated formally at $f_j(x)=Q_jx$ and $\delta_j=t_0j^{-\alpha}$," "\n"
     r"is $\liminf_n(\log Q_n+\sum_{j<n}\log\delta_j)/(\log Q_n-\log\delta_n)=1-\alpha/r$,",
     r"evaluated formally at $f_j(x)=Q_jx$ and $\delta_j=\kappa j^{-\alpha}$ ($\kappa>0$, $j\ge1$)," "\n"
     r"is $\liminf_n(\log Q_n+\sum_{1\le j<n}\log\delta_j)/(\log Q_n-\log\delta_n)=1-\alpha/r$,"),
    (r"proof above does not use that condition. (Hypotheses as stated in arXiv:1710.03596v1.)",
     r"proof above does not use that condition. " + BAKER),
    # rem:growing-BLR
    (r"\cite{BLR} already gives $\dimH E_{G,0,\mathrm{lim}}(0)=1$, hence also",
     r"\cite{BLR} (stated there without proof) already gives" "\n"
     r"$\dimH E_{G,0,\mathrm{lim}}(0)=1$, hence also"),
    (r"$\dimH E_{G,0}(t)=1$. For $\tau>0$ and $\lim_{j\to\infty}\log A_j/\log Q_j=\infty$",
     r"$\dimH E_{G,0}(t)=1$. For $0<\tau<1$ and $\lim_{j\to\infty}\log A_j/\log Q_j=\infty$"),
    (r"\cite[Theorem~7]{BLR}, its dimension formula gives $0$, and",
     r"\cite[Theorem~7]{BLR}, its formula gives local dimension $0$ at every point (hence" "\n"
     r"Hausdorff dimension $0$, covering $\R$ by countably many bounded intervals), and"),
    (r"yields $\dimH E_{G,\tau}(t)=0$ by countable stability. In all other cases---in",
     r"yields $\dimH E_{G,\tau}(t)=0$ by countable stability, hence also" "\n"
     r"$\dimH E_{G,\tau,\mathrm{lim}}(0)=0$ since $E_{G,\tau,\mathrm{lim}}(0)\subseteq E_{G,\tau}(t)$." "\n"
     r"In all other cases---in"),
    (r"right-hand side, evaluated formally at $f_j(x)=Q_jx$ and $\delta_j=cA_j^{-\tau}$, is",
     r"right-hand side, evaluated formally at $f_j(x)=Q_jx$ and $\delta_j=\kappa A_j^{-\tau}$" "\n"
     r"($\kappa>0$, $j\ge J_0$), is"),
    (r"nevertheless $(1-\tau)/(1+\tau\gamma_{\sup})$ (using $\log Q_n=\sum_{j<n}\log A_j+O(n)$",
     r"nevertheless $(1-\tau)/(1+\tau\gamma_{\sup})$ (using $\log Q_n=\sum_{J_0\le j<n}\log A_j+O(n)$"),
    (r"of that formula beyond condition~(1.6). (Hypotheses as stated in arXiv:1710.03596v1.)",
     r"of that formula beyond condition~(1.6). " + BAKER),
]


def main():
    texts = {f: f.read_text(encoding="utf-8") for f in FILES}
    for old, new in EDITS:
        total = 0
        for f in FILES:
            n = texts[f].count(old)
            assert n <= 1, (f.name, n, old[:60])
            if n:
                texts[f] = texts[f].replace(old, new)
                total += 1
        assert total >= 1, ("anchor not found anywhere", old[:70])
    for f in FILES:
        if texts[f] != f.read_text(encoding="utf-8"):
            f.write_text(texts[f], encoding="utf-8")
            print("patched", f.relative_to(HERE))


if __name__ == "__main__":
    main()
