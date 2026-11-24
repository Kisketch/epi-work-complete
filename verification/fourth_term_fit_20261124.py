r"""Numerical test of a HEURISTIC fourth-order term in thm:multi-residue-asymptotic (2026-11-24).

Classification (AGENTS.md): 有限计算 / 数值佐证 + 启发式猜想.  Nothing here is a proof.

Heuristic.  With eps = 2 dimH - 1, the scalar model (from m^{-1-eps} zeta(1+eps) ~ (1/eps+gamma)/m)
        eps m = (C - eps C') (1 + gamma eps) m^{-eps}
reproduces the PROVED terms of eq:multi-dimH-three-term exactly (d=1); expanding it one order
further gives the leading next term
        dimH F_{m,r} = 1/2 + C/(2m) - C^2 L/(2m^2) + C(gamma C - C')/(2m^2) + (3/4) C^3 L^2/m^3 + O(L/m^3),
L = log m.  (The model ignores the x-dependence of the eigenfunction, which can change the
O(L/m^3) and O(1/m^3) coefficients; only the L^2/m^3 coefficient is predicted.)

Primary test (ansatz-free): solve the scalar model exactly for each m (eps_m) and check that
        m^3 (dim - (1+eps_m)/2) / L^2  -> 0,
which says model and true dimension share all terms down to and including L^2/m^3.  The symbolic
expansion of the model (sympy, printed below) gives the 1/m^3 coefficient.  Secondary diagnostic:
free least-squares fit R = A L^2 + B L + D, R := m^3 (dim - three-term) -- ILL-CONDITIONED
(L <= 10, so L^2 and L are hard to separate; higher orders contaminate small m); reported only
to show this.  Data: asymptotic_residues_check_20261123.partial.jsonl (this repo,
n=16/24 collocation, m <= 1024) and verify_residue_multi_asymptotic.json (independent script by
the author, m up to 16384) where present.
"""
import json
from pathlib import Path

from mpmath import mp, mpf, log, euler, exp, matrix, lu_solve

mp.dps = 40
HERE = Path(__file__).resolve().parent


def consts(r, terms=600):
    q0, q1 = mpf(1), mpf(r)
    C, Cp = mpf(1), mpf(0)
    for _ in range(terms):
        C += 1 / q1
        Cp += log(q1) / q1
        q0, q1 = q1, r * q1 + q0
    return C, Cp


def three_term(m, C, Cp):
    m = mpf(m)
    return mpf(1) / 2 + C / (2 * m) - C ** 2 * log(m) / (2 * m ** 2) + C * (euler * C - Cp) / (2 * m ** 2)


def model_dim(m, C, Cp):
    """(1+eps)/2 with eps the root near C/m of eps m = (C - eps C')(1 + gamma eps) m^{-eps}."""
    L = log(m)
    g = lambda e: (C - e * Cp) * (1 + euler * e) * exp(-e * L) - e * m
    lo, hi = mpf(0), 2 * C / m              # g(0) = C > 0; bracket checked, then bisection
    while g(hi) > 0:
        hi *= 2
    for _ in range(160):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if g(mid) > 0 else (lo, mid)
    return (1 + (lo + hi) / 2) / 2


def symbolic_model_expansion():
    import sympy as sp
    h, L, C, Cp, g = sp.symbols("h L C Cp gamma", positive=True)
    u0, u1, u2 = sp.symbols("u0 u1 u2")
    u = u0 + u1 * h + u2 * h ** 2           # u = eps * m, h = 1/m, L = log m treated as independent
    eps = u * h
    ser = sp.series((C - eps * Cp) * (1 + g * eps) * sp.exp(-eps * L) - u, h, 0, 3).removeO()
    sol = {}
    for k, uk in enumerate((u0, u1, u2)):
        sol[uk] = sp.solve(sp.expand(ser.coeff(h, k).subs(sol)), uk)[0]
    delta = sp.expand((u * h / 2).subs(sol))
    return [f"  1/m^{k}: {sp.collect(sp.expand(delta.coeff(h, k)), L)}" for k in (1, 2, 3)]


def lsq(rows, ys):
    k = len(rows[0])
    AtA = matrix(k, k)
    Atb = matrix(k, 1)
    for row, y in zip(rows, ys):
        for i in range(k):
            Atb[i] += row[i] * y
            for j in range(k):
                AtA[i, j] += row[i] * row[j]
    return lu_solve(AtA, Atb)


def load():
    """Return {label: (dC, dC', {m: (dim, source)})} with dC = d*C_S, dC' = d*C_S'."""
    cases = {}
    for key in (1, 2, 3, "m"):
        C, Cp = (mpf(1), mpf(0)) if key == "m" else consts(key)
        cases["r=m (B={0})" if key == "m" else f"r={key}"] = (C, Cp, {})
    for line in (HERE / "asymptotic_residues_check_20261123.partial.jsonl").read_text().splitlines():
        d = json.loads(line)
        if d["m"] < 8 or not (d["r"] == d["m"] or d["m"] > 2 * d["r"]):
            continue
        label = "r=m (B={0})" if d["r"] == d["m"] else f"r={d['r']}"
        cases[label][2][d["m"]] = (mpf(d["dim_n26"]), "repo-n24")
    author = HERE / "verify_residue_multi_asymptotic.json"
    if author.exists():
        for c in json.loads(author.read_text())["multi_subcritical"]:
            dd = len(c["S"]) + len(c["B"])
            dC, dCp = dd * mpf(c["C_S"]), dd * mpf(c["C_S_prime"])
            if c["label"] in cases:
                C0 = cases[c["label"]][0]
                assert abs(C0 - dC) < mpf(10) ** -15, ("C mismatch", c["label"], C0, dC)
            else:
                cases[c["label"]] = (dC, dCp, {})
            for row in c["rows"]:
                if row["m"] not in cases[c["label"]][2]:   # repo n=24 value preferred where both exist
                    cases[c["label"]][2][row["m"]] = (mpf(row["dim"]), "author-n16")
                else:
                    other = cases[c["label"]][2][row["m"]][0]
                    assert abs(other - mpf(row["dim"])) < mpf(10) ** -12, ("cross-script mismatch", c["label"], row["m"])
    return cases


def main():
    cases = load()
    out = ["# NON-RIGOROUS: collocation estimates; heuristic fourth term (3/4) (dC_S)^3 log^2 m / m^3",
           "# R(m) = m^3 (dim - three-term);  fit R = A L^2 + B L + D on m >= M0"]
    out.append("\n== Symbolic expansion of the scalar model: dim - 1/2 =")
    out.extend(symbolic_model_expansion())
    out.append("\n== PRIMARY TEST: m^3 (dim - model)/L^2  [and m^3 (dim - model)/L]  (should -> 0 [stay bounded])")
    for label, (C, Cp, pts) in cases.items():
        row = []
        for m in sorted(pts):
            if m >= 64:
                diff = (pts[m][0] - model_dim(m, C, Cp)) * mpf(m) ** 3
                row.append(f"{m}:{float(diff / log(m) ** 2):+.3f}[{float(diff / log(m)):+.2f}]")
        out.append(f"  {label:16s} dC/m_max={float(C / max(pts)):.4f}  " + "  ".join(row))
    out.append("\n== SECONDARY (ill-conditioned) free fits")
    summary = []
    for label, (C, Cp, pts) in cases.items():
        pred = mpf(3) / 4 * C ** 3
        out.append(f"\n== {label}: dC={float(C):.12f} dC'={float(Cp):.12f} predicted A=(3/4)(dC)^3={float(pred):.6f}")
        pts = sorted(pts.items())
        for m, (dim, src) in pts:
            L = log(m)
            R = (dim - three_term(m, C, Cp)) * mpf(m) ** 3
            out.append(f"  m={m:6d} R/L^2={float(R / L ** 2):+.5f}  (R-predL^2)/L={float((R - pred * L ** 2) / L):+.5f}  [{src}]")
        best = None
        for M0 in (64, 128, 256):
            sel = [(m, d) for m, (d, _) in pts if m >= M0]
            if len(sel) < 4:
                continue
            rows = [[log(m) ** 2, log(m), mpf(1)] for m, _ in sel]
            ys = [(d - three_term(m, C, Cp)) * mpf(m) ** 3 for m, d in sel]
            A, B, D = lsq(rows, ys)
            best = (M0, len(sel), A / pred, max(m for m, _ in sel))
            out.append(f"  fit m>={M0} ({len(sel)} pts, m<={best[3]}): A={float(A):+.4f} (pred {float(pred):.4f}, ratio {float(A / pred):.4f})  B={float(B):+.3f}  D={float(D):+.3f}")
        if best:
            summary.append(f"  {label:18s} fit m>={best[0]:4d} ({best[1]} pts, m<={best[3]}): A/pred = {float(best[2]):.4f}")
    out.append("\n== SUMMARY of free fits (largest-M0 fit per case; NOT a reliable estimate of A, see docstring)")
    out.extend(summary)
    text = "\n".join(out)
    print(text)
    (HERE / "fourth_term_fit_20261124.log").write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
