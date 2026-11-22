"""Reproducible symbolic verification of the 12 algebraic steps in Paper 1 (Appendix A.1)."""
from pathlib import Path
import sympy as sp


def main() -> None:
    lines = []
    lines.append(f"SymPy version: {sp.__version__}")

    x, r, s, S, P, D, rho = sp.symbols("x r s S P D rho", positive=True)
    e_sym, pi_sym = sp.symbols("e_sym pi_sym", positive=True)
    n, k = sp.symbols("n k", integer=True, positive=True)

    checks = []

    # 1. Vieta's root identity
    poly_vieta = sp.expand((x - e_sym) * (x - pi_sym) - (x**2 - (e_sym + pi_sym) * x + e_sym * pi_sym))
    assert poly_vieta == 0
    checks.append(("1. Vieta root identity", True))

    # 2-7. Six pair solves of Theorem thm:four
    # Pair 1: e+pi = r, e-pi = s -> solve for e, pi
    sol1 = sp.solve([e_sym + pi_sym - r, e_sym - pi_sym - s], (e_sym, pi_sym))
    assert sp.simplify(sol1[e_sym] - (r + s) / 2) == 0
    assert sp.simplify(sol1[pi_sym] - (r - s) / 2) == 0
    checks.append(("2. Pair 1 (e+pi, e-pi)", True))

    # Pair 2: e+pi = r, e*pi = s -> quadratic roots satisfy x^2 - r*x + s = 0
    roots2 = sp.solve(x**2 - r * x + s, x)
    assert sp.simplify(roots2[0] + roots2[1] - r) == 0
    assert sp.simplify(roots2[0] * roots2[1] - s) == 0
    checks.append(("3. Pair 2 (e+pi, e*pi)", True))

    # Pair 3: e-pi = r, e*pi = s -> e and -pi satisfy x^2 - r*x - s = 0
    roots3 = sp.solve(x**2 - r * x - s, x)
    assert sp.simplify(roots3[0] + roots3[1] - r) == 0
    assert sp.simplify(roots3[0] * (-roots3[1]) - s) == 0
    checks.append(("4. Pair 3 (e-pi, e*pi)", True))

    # Pair 4: e+pi = r, e/pi = s -> pi = r/(s+1)
    sol4 = sp.solve([e_sym + pi_sym - r, e_sym / pi_sym - s], (e_sym, pi_sym))
    assert sp.simplify(sol4[pi_sym] - r / (s + 1)) == 0
    checks.append(("5. Pair 4 (e+pi, e/pi)", True))

    # Pair 5: e-pi = r, e/pi = s -> pi = r/(s-1) for s != 1
    sol5 = sp.solve([e_sym - pi_sym - r, e_sym / pi_sym - s], (e_sym, pi_sym))
    assert sp.simplify(sol5[pi_sym] - r / (s - 1)) == 0
    checks.append(("6. Pair 5 (e-pi, e/pi)", True))

    # Pair 6: e*pi = r, e/pi = s -> e^2 = r*s
    sol6 = sp.simplify((e_sym * pi_sym) * (e_sym / pi_sym) - e_sym**2)
    assert sol6 == 0
    checks.append(("7. Pair 6 (e*pi, e/pi)", True))

    # 8. Translation identity: mu0 = log(D/rho)/log(D) = 1 + 1/(M - 1) where M = 1 + log(D)/log(1/rho)
    M_expr = 1 + sp.log(D) / sp.log(1 / rho)
    mu0_lhs = sp.log(D / rho) / sp.log(D)
    mu0_rhs = 1 + 1 / (M_expr - 1)
    assert sp.simplify(sp.expand_log(mu0_lhs - mu0_rhs, force=True)) == 0
    checks.append(("8. Translation identity mu0 = 1 + 1/(M-1)", True))

    # 9. Termwise recurrence identity: (n+1) * n!/k! = (n+1)!/k!
    rec_diff = sp.simplify((n + 1) * sp.factorial(n) / sp.factorial(k) - sp.factorial(n + 1) / sp.factorial(k))
    assert rec_diff == 0
    checks.append(("9. Termwise recurrence (n+1)*n!/k! = (n+1)!/k!", True))

    # 10. Gauss integral: int_0^oo exp(-x^2) dx = sqrt(pi)/2
    I_gauss = sp.integrate(sp.exp(-(x**2)), (x, 0, sp.oo))
    assert sp.simplify(I_gauss - sp.sqrt(sp.pi) / 2) == 0
    checks.append(("10. Gauss integral", True))

    # 11. Mixed integral: int_0^pi exp(x)*sin(x) dx = (exp(pi) + 1)/2
    I_mixed = sp.integrate(sp.exp(x) * sp.sin(x), (x, 0, sp.pi))
    assert sp.simplify(I_mixed - (sp.exp(sp.pi) + 1) / 2) == 0
    checks.append(("11. Mixed integral", True))

    # 12. Stirling limit: lim_{n->oo} n! * e^n / (n^n * sqrt(2*pi*n)) = 1
    stirling = sp.limit(sp.factorial(n) * sp.E**n / (n**n * sp.sqrt(2 * sp.pi * n)), n, sp.oo)
    assert stirling == 1
    checks.append(("12. Stirling limit", True))

    assert len(checks) == 12
    for label, ok in checks:
        lines.append(f"  [PASS] {label}: {ok}")
    lines.append("ALL 12/12 SYMBOLIC CHECKS PASSED.")

    out = "\n".join(lines) + "\n"
    log_path = Path(__file__).resolve().parent / "verify_round3.log"
    log_path.write_text(out, encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
