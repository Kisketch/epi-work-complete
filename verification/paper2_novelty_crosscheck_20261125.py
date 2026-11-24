"""Cross-checks for verification/paper2_novelty_review_20261125.md.

All checks are symbolic or numerical sanity checks.  This script proves no
new theorem.  Run:  python verification/paper2_novelty_crosscheck_20261125.py

(A) Leading-log tower of the scalar model of rem:fourth-term
    eps*m = Gamma*m^(-eps)  (gamma = Gamma' = 0).
    Claim: eps = W(Gamma*L/m)/L with L = log m, so the coefficient of
    L^(n-1)/m^n in dimH - 1/2 = eps/2 is (-n)^(n-1) Gamma^n / (2 n!).
    For n = 3 this gives 3 Gamma^3/4, the coefficient conjectured in rem:fourth-term.
(B) DFSU (arXiv:2007.10554v2, eq. (1.4)):
    c_{i,i-1} = -2^(i-1) i^(i-2)/(i-1)! (6/pi^2)^i.
    Check that this is -(1/2) i^(i-1)/i! (2c)^i with c = 6/pi^2, i.e. the
    same Lambert-W tree-function coefficients, with z = 2cL/N and no sign
    alternation (removing branches instead of adding them).
    Also check that 72/pi^4 = 2(6/pi^2)^2 (Hensley's c_{2,1}).
(C) Full scalar model of rem:fourth-term:
    eps*m = (Gamma - eps*Gamma')(1 + gamma*eps) m^(-eps).
    Re-derive the four proved terms and the (log m)^2/m^3 coefficient.
(D) Heinemann-Urbanski bound (as stated in CLU arXiv:1805.11904v1, Thm 2.4,
    with the Lyapunov lower bound from CLU Prop. 2.6) evaluated for
    S={1,2}, B=empty: compare the resulting constant with the collocation
    value m^{2 s0}(dimH - s0) ~ 28.78 at m=4096 that the paper reports
    (tab:multi-residue-asymptotic caption).  The constant must not be smaller.
"""
import sympy as sp
import mpmath as mp

print("=== (A) Lambert-W leading-log tower of eps*m = Gamma*m^(-eps) ===")
G, x, L = sp.symbols('Gamma x L', positive=True)  # x = 1/m
# Solve u*e^u = z with u = eps*L, z = Gamma*L*x; W series:
z = G * L * x
N = 6
W_series = sum(((-n) ** (n - 1)) * z ** n / sp.factorial(n) for n in range(1, N + 1))
eps_series = sp.expand(W_series / L)
# Verify that the series satisfies eps = Gamma*x*exp(-eps*L) up to order x^N
resid = sp.series(eps_series - G * x * sp.exp(-eps_series * L), x, 0, N + 1).removeO()
print("residual of model equation up to x^%d:" % N, sp.simplify(resid))
for n in range(1, 6):
    coeff = sp.simplify(sp.expand(eps_series / 2).coeff(x, n))
    print(f"  n={n}: coefficient of x^{n} in dimH-1/2 = {coeff}")
c3 = sp.simplify(sp.expand(eps_series / 2).coeff(x, 3) / L ** 2)
print("  n=3 coefficient / L^2 =", c3, "; equals 3*Gamma^3/4 ?", sp.simplify(c3 - sp.Rational(3, 4) * G ** 3) == 0)

print("\n=== (B) DFSU eq. (1.4) is the same tree-function pattern ===")
c = sp.Symbol('c', positive=True)
for i in range(1, 8):
    dfsu = -sp.Integer(2) ** (i - 1) * sp.Integer(i) ** (i - 2) / sp.factorial(i - 1) * c ** i
    lam = -sp.Rational(1, 2) * sp.Integer(i) ** (i - 1) / sp.factorial(i) * (2 * c) ** i
    print(f"  i={i}: DFSU c_(i,i-1) = {sp.simplify(dfsu)};  -(1/2) i^(i-1)/i! (2c)^i = {sp.simplify(lam)};  equal: {sp.simplify(dfsu - lam) == 0}")
print("  72/pi^4 - 2*(6/pi^2)^2 =", sp.simplify(72 / sp.pi ** 4 - 2 * (6 / sp.pi ** 2) ** 2))
# Residue family: coefficient of L^(n-1)/m^n is (1/2)(-n)^(n-1)/n! Gamma^n
# = -(1/2) n^(n-1)/n! (-Gamma)^n, i.e. DFSU's pattern with 2c -> -Gamma.
for n in range(1, 6):
    a = sp.Rational(1, 2) * (-n) ** (n - 1) / sp.factorial(n) * G ** n
    b = -sp.Rational(1, 2) * sp.Integer(n) ** (n - 1) / sp.factorial(n) * (-G) ** n
    assert sp.simplify(a - b) == 0
print("  residue-family tower = DFSU pattern with 2c replaced by -Gamma (checked n=1..5)")

print("\n=== (C) Full scalar model of rem:fourth-term ===")
Gp, gam = sp.symbols("Gammap gamma_E", real=True)
# Ansatz eps = a1 x + (a2 L + b2) x^2 + (a3 L^2 + b3 L + c3) x^3, x = 1/m, m^(-eps) = exp(-eps L)
a1, a2, b2, a3, b3, c3s = sp.symbols('a1 a2 b2 a3 b3 c3')
eps = a1 * x + (a2 * L + b2) * x ** 2 + (a3 * L ** 2 + b3 * L + c3s) * x ** 3
eq = eps - x * (G - eps * Gp) * (1 + gam * eps) * sp.exp(-eps * L)
ser = sp.expand(sp.series(eq, x, 0, 4).removeO())
eqs = []
for k in range(1, 4):
    ck = sp.expand(ser.coeff(x, k))
    eqs += [sp.Eq(ck.coeff(L, j), 0) for j in range(0, 3)]
sol = sp.solve(eqs, [a1, a2, b2, a3, b3, c3s], dict=True)[0]
half = {k: sp.simplify(v / 2) for k, v in sol.items()}
print("  dimH-1/2 coefficients (x=1/m):")
print("    1/m          :", half[a1])
print("    log m/m^2    :", half[a2])
print("    1/m^2        :", sp.factor(half[b2]))
print("    (log m)^2/m^3:", half[a3])
print("    log m/m^3    :", sp.factor(half[b3]), "  (not claimed by the paper)")
print("  1/m^2 term equals Gamma(gamma*Gamma-Gamma')/2 ?", sp.simplify(half[b2] - G * (gam * G - Gp) / 2) == 0)
print("  (log m)^2/m^3 term equals 3 Gamma^3/4 ?", sp.simplify(half[a3] - sp.Rational(3, 4) * G ** 3) == 0)

print("\n=== (D) Heinemann-Urbanski upper bound for S={1,2}, B=empty ===")
mp.mp.dps = 30
s0 = mp.mpf('0.531280506')  # value reported in the paper (non-rigorous collocation)
K = 4                          # distortion constant when 1 is in the alphabet (CLU v1, text after Thm 2.4)
chi_lb = 2 * mp.log((1 + mp.sqrt(5)) / 2)  # CLU Prop. 2.6 with k=1
# tail digits a = km+1, km+2 (k>=1) are > km, so sum a^(-2 s0) <= 2 m^(-2 s0) zeta(2 s0)
const = K ** s0 / chi_lb * 2 * mp.zeta(2 * s0)
print("  K^s0 / chi_lb * 2 zeta(2 s0) =", mp.nstr(const, 12))
print("  paper's collocation value of m^(2 s0)(dimH - s0) at m=4096: 28.78")
print("  bound >= reported value ?", const >= mp.mpf('28.78'))
