"""Reproducible cosine integral check and 450-digit mpmath interval certificate (Paper 1 Appendix A)."""
import json
from pathlib import Path
import sympy as sp
from mpmath import iv, mp


def main() -> None:
    lines = []
    lines.append("=== Round 4 Verification: Cosine Integral & 450-digit Interval Certificate ===")

    # 1. Cosine integral: int_0^oo cos(x)/(1+x^2) dx = pi / (2e)
    x = sp.Symbol("x", real=True)
    cos_int_sym = sp.integrate(sp.cos(x) / (1 + x**2), (x, 0, sp.oo))
    target_sym = sp.pi / (2 * sp.E)
    sym_ok = sp.simplify(cos_int_sym - target_sym) == 0
    assert sym_ok, f"SymPy mismatch: {cos_int_sym} vs {target_sym}"
    lines.append(f"[PASS] SymPy cosine integral: {cos_int_sym} == {target_sym}")

    # Cross-check numerically with 80-digit oscillatory quadrature
    mp.dps = 80
    cos_num = mp.quadosc(lambda t: mp.cos(t) / (1 + t**2), [0, mp.inf], omega=1)
    cos_err = abs(cos_num - mp.pi / (2 * mp.e))
    assert cos_err < mp.mpf("1e-50"), f"Numerical cosine integral error: {cos_err}"
    lines.append(f"[PASS] High-precision oscillatory quadrature agreement: |err| = {mp.nstr(cos_err, 6)}")

    # 2. 450-digit directed-rounding interval arithmetic for e + pi
    iv.dps = 460  # guard digits to certify width < 9.13e-451 at >= 450 decimal digits
    e_iv = iv.exp(iv.mpf(1))
    pi_iv = iv.pi
    s_iv = e_iv + pi_iv
    mp.dps = 470
    L = mp.mpf(s_iv.a)
    U = mp.mpf(s_iv.b)
    width = mp.mpf((s_iv.b - s_iv.a).b)
    assert width < mp.mpf("9.13e-451"), f"Interval width too large: {width}"
    lines.append(f"[PASS] e + pi enclosed in [L, U] with width <= {mp.nstr(width, 6)} < 9.13e-451")

    # Certificate 1: for all 1 <= q <= 1000, open interval (L*q, U*q) contains no integer
    cert1_fail = []
    for q in range(1, 1001):
        q_iv = s_iv * q
        lq = mp.mpf(q_iv.a)
        uq = mp.mpf(q_iv.b)
        k = int(mp.floor(lq))
        if not (mp.mpf(k) < lq and uq < mp.mpf(k + 1)):
            cert1_fail.append(q)
    assert not cert1_fail, f"Certificate 1 failures: {cert1_fail}"
    lines.append("[PASS] Certificate 1: for all 1 <= q <= 1000, (L*q, U*q) contains no integer")

    # Certificate 2: Proposition prop:window for 1 <= n <= 60
    # prop:window requires B_n - 1/n < n! * pi < B_n for integer B_n, equivalently 1 - 1/n < {n! * pi} < 1.
    violated_n = []
    passing_n = []
    for n in range(1, 61):
        nf = int(sp.factorial(n))
        prod_iv = iv.mpf(nf) * pi_iv
        p_lo = mp.mpf(prod_iv.a)
        p_hi = mp.mpf(prod_iv.b)
        fl_lo = int(mp.floor(p_lo))
        fl_hi = int(mp.floor(p_hi))
        assert fl_lo == fl_hi, f"Floor ambiguity at n={n}"
        frac_iv = prod_iv - fl_lo
        thresh_iv = iv.mpf(1) - iv.mpf(1) / n
        if mp.mpf(frac_iv.b) <= mp.mpf(thresh_iv.a):
            violated_n.append(n)
        else:
            assert mp.mpf(frac_iv.a) > mp.mpf(thresh_iv.b), f"Ambiguous window boundary at n={n}"
            passing_n.append(n)

    expected_violated = [2, 4] + [n for n in range(7, 61) if n != 34]
    assert violated_n == expected_violated, f"Violated mismatch: {violated_n} vs {expected_violated}"
    assert passing_n == [1, 3, 5, 6, 34], f"Passing mismatch: {passing_n}"
    lines.append(f"[PASS] Certificate 2: window condition violated at n=2, 4, and 7<=n<=60 except n=34 (passing in 1..60: {passing_n})")

    # For every 1 <= q <= 60, find smallest n >= q that is certified violated
    first_violation = {}
    for q in range(1, 61):
        cand = [n for n in violated_n if n >= q]
        assert cand, f"No certified violation >= {q}"
        first_violation[str(q)] = cand[0]
    assert first_violation["34"] == 35, f"q=34 first violation: {first_violation['34']}"
    lines.append("[PASS] Every q <= 60 has certified first violation (q=34 -> n=35)")

    cert_data = {
        "iv_dps": iv.dps,
        "width_str": mp.nstr(width, 10),
        "width_lt_9_13e_451": bool(width < mp.mpf("9.13e-451")),
        "e_plus_pi_prefix_50": mp.nstr(L, 50),
        "irrationality_den_checked_up_to": 1000,
        "all_q_le_1000_no_integer": True,
        "window_n_range": [1, 60],
        "window_violated_n": violated_n,
        "window_passing_n_in_1_60": passing_n,
        "first_violation_for_q_le_60": first_violation,
    }
    out_dir = Path(__file__).resolve().parent
    (out_dir / "certificate_round4.json").write_text(
        json.dumps(cert_data, indent=2) + "\n", encoding="utf-8"
    )
    out_txt = "\n".join(lines) + "\n"
    (out_dir / "verify_round4.log").write_text(out_txt, encoding="utf-8")
    print(out_txt)


if __name__ == "__main__":
    main()
