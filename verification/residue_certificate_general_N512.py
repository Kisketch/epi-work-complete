"""Exact integer transfer-operator certificates, N=512 variant.

Same method as residue_certificate_general.py (GRID=256) but with GRID=512 spatial
cells to recover the one-cell slack observed at r=1 for m in {2,3,4,6}.
The s reporting grid stays 1/512; outputs go to residue_certificate_general_N512.log/.json
and never overwrite the GRID=256 originals.
"""
from __future__ import annotations

import json
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

GRID = 512
SCALE = 10**13
FINITE_DIGITS = 2**80


@lru_cache(maxsize=None)
def enclose_power(base: Fraction, power: Fraction) -> tuple[int, int]:
    """Return integer bounds [lo, hi] for SCALE * base**(-power), checked in exact Z."""
    p, q = power.numerator, power.denominator
    proposal = int(SCALE * float(base) ** (-float(power)))
    rhs = SCALE**q * base.denominator**p
    factor = base.numerator**p
    lo, hi = max(0, proposal - 1), proposal + 2
    while lo**q * factor > rhs and lo > 0:
        lo -= 1
    while hi**q * factor < rhs:
        hi += 1
    if not (lo**q * factor <= rhs <= hi**q * factor):
        raise ArithmeticError(f"Integer check failed for {base}^(-{power})")
    return lo, hi


def cell(a: int, endpoint: int) -> int:
    return min(GRID - 1, GRID**2 // (a * GRID + endpoint))


def first_tail_index(m: int, r: int) -> int:
    # Ensure m * K + 1 > GRID so every tail image 1/(m*k + r + x) falls strictly inside C_0.
    return max(120, GRID // m + 2)


def coefficients(m: int, r: int, s: Fraction, finite_digits: int = FINITE_DIGITS):
    k_cut = first_tail_index(m, r)
    power = 2 * s
    integral_factor = Fraction(1, m) / (power - 1)
    assert m * k_cut + r > GRID
    lower_start, _ = enclose_power(Fraction(m * k_cut + r + 1), power - 1)
    _, upper_end = enclose_power(Fraction(m * finite_digits + r + 1), power - 1)
    _, upper_start = enclose_power(Fraction(m * (k_cut - 1) + r), power - 1)
    lower_tail = int(integral_factor * (lower_start - upper_end))
    upper_tail = int(-(-integral_factor * upper_start // 1))
    assert lower_tail > 0
    rows = []
    for j in range(GRID):
        row = []
        for k in range(k_cut):
            a = m * k + r
            lo, _ = enclose_power(Fraction(a * GRID + j + 1, GRID), power)
            _, hi = enclose_power(Fraction(a * GRID + j, GRID), power)
            row.append((lo, hi, cell(a, j + 1), cell(a, j)))
        rows.append(row)
    return rows, lower_tail, upper_tail, k_cut


def provisional_vector(rows, tail: int) -> list[int]:
    """Compute a strictly positive rational/integer step vector (heuristic only)."""
    vector = [1.0] * GRID
    for _ in range(45):
        nxt = [
            (
                sum(
                    (lo + hi) * (vector[left] + vector[right]) / 4.0
                    for lo, hi, left, right in row
                )
                + tail * vector[0]
            )
            / SCALE
            for row in rows
        ]
        s0 = nxt[0]
        vector = [val / s0 for val in nxt]
    return [max(1, round(10**9 * val)) for val in vector]


def certify_side(m: int, r: int, s: Fraction, side: str, finite_digits: int = FINITE_DIGITS):
    rows, lower_tail, upper_tail, k_cut = coefficients(m, r, s, finite_digits=finite_digits)
    vector = provisional_vector(rows, (lower_tail + upper_tail) // 2)
    margins: list[Fraction] = []
    for j, row in enumerate(rows):
        bound = SCALE * vector[j]
        if side == "lower":
            val = sum(lo * min(vector[left : right + 1]) for lo, _hi, left, right in row)
            margins.append(Fraction(val + lower_tail * vector[0] - bound, bound))
        else:
            val = sum(hi * max(vector[left : right + 1]) for _lo, hi, left, right in row)
            margins.append(Fraction(bound - val - upper_tail * vector[0], bound))
    res = min(margins)
    enclose_power.cache_clear()
    return res, k_cut


def find_certified_bracket(m: int, r: int, lo_guess: int, hi_guess: int):
    """Find tight certified dyadic bracket [k_lo/512, k_hi/512] of width <= 1/256."""
    best_lo = None
    for k in range(lo_guess + 2, lo_guess - 6, -1):
        s = Fraction(k, 512)
        margin, _ = certify_side(m, r, s, "lower")
        if margin > 0:
            best_lo = (k, s, margin)
            break
    assert best_lo is not None, f"Failed lower bound for m={m}, r={r}"

    best_hi = None
    for k in range(hi_guess - 2, hi_guess + 6):
        s = Fraction(k, 512)
        margin, k_cut = certify_side(m, r, s, "upper")
        if margin > 0:
            best_hi = (k, s, margin, k_cut)
            break
    assert best_hi is not None, f"Failed upper bound for m={m}, r={r}"
    width = best_hi[1] - best_lo[1]
    assert width <= Fraction(1, 256), f"Width too large for m={m}, r={r}: {width}"
    return best_lo, best_hi


def main() -> None:
    # Accurate estimates in units of 1/512 for (m, r) across m = 2..6 and r in {1, m}
    targets = [
        (2, 1, 420, 421),  # E_odd  ~ 0.82115 (420/512 = 0.82031, 421/512 = 0.82227)
        (2, 2, 368, 369),  # E_even ~ 0.71925 (368/512 = 0.71875, 369/512 = 0.72070)
        (3, 1, 380, 381),  # F_{3,1}~ 0.74348 (380/512 = 0.74219, 381/512 = 0.74414)
        (3, 3, 327, 329),  # F_{3,3}: GRID=256 cert proves dimH >= 41/64 = 0.640625 (old ~0.6395 comment was a coarse estimate, do not use as target)
        (4, 1, 357, 359),  # F_{4,1}~ 0.6989  (357/512 = 0.69727, 359/512 = 0.70117)
        (4, 4, 309, 311),  # F_{4,4}~ 0.6045  (309/512 = 0.60352, 311/512 = 0.60742)
        (5, 1, 342, 344),  # F_{5,1}~ 0.6691  (342/512 = 0.66797, 344/512 = 0.67188)
        (5, 5, 298, 300),  # F_{5,5}~ 0.5837  (298/512 = 0.58203, 300/512 = 0.58594)
        (6, 1, 331, 333),  # F_{6,1}~ 0.6476  (331/512 = 0.64648, 333/512 = 0.65039)
        (6, 6, 291, 293),  # F_{6,6}~ 0.5701  (291/512 = 0.56836, 293/512 = 0.57227)
    ]
    results = []
    log_lines = [
        "=== General Modulus m in {2,3,4,5,6} Exact Integer Residue Certificates ===",
        f"GRID={GRID}, FINITE_DIGITS={FINITE_DIGITS}, SCALE={SCALE}",
    ]
    by_mod: dict[int, dict[int, dict]] = {}
    for m, r, gl, gh in targets:
        lo_info, hi_info = find_certified_bracket(m, r, gl, gh)
        k_lo, s_lo, m_lo = lo_info
        k_hi, s_hi, m_hi, k_cut = hi_info
        width = s_hi - s_lo
        rec = {
            "modulus": m,
            "residue": r,
            "k_tail": k_cut,
            "lower": str(s_lo),
            "lower_float": float(s_lo),
            "lower_margin": float(m_lo),
            "lower_margin_exact": str(m_lo),
            "upper": str(s_hi),
            "upper_float": float(s_hi),
            "upper_margin": float(m_hi),
            "upper_margin_exact": str(m_hi),
            "width": str(width),
        }
        results.append(rec)
        by_mod.setdefault(m, {})[r] = rec
        line = (
            f"m={m}, r={r:d} (K={k_cut}): {s_lo} ({float(s_lo):.6f}) < dimH < {s_hi} ({float(s_hi):.6f}) "
            f"| width={width} | margins=({float(m_lo):+.6f}, {float(m_hi):+.6f})"
        )
        print(line, flush=True)
        log_lines.append(line)

    # Check strict sandwich separation upper(F_{m,m}) < lower(F_{m,1}) and m=4 reference match
    for m in (2, 3, 4, 5, 6):
        lo_max = Fraction(by_mod[m][1]["lower"])
        hi_min = Fraction(by_mod[m][m]["upper"])
        assert hi_min < lo_max, f"No strict separation at m={m}: {hi_min} vs {lo_max}"
        sep_line = f"  [PASS] Strict gap at m={m}: upper(F_{{{m},{m}}})={hi_min} < lower(F_{{{m},1}})={lo_max}"
        print(sep_line, flush=True)
        log_lines.append(sep_line)

    assert Fraction(by_mod[4][1]["lower"]) >= Fraction(357, 512)
    assert Fraction(by_mod[4][1]["upper"]) <= Fraction(359, 512)
    assert certify_side(4, 1, Fraction(357, 512), "lower")[0] > 0
    assert certify_side(4, 1, Fraction(359, 512), "upper")[0] > 0
    print("  [PASS] m=4 F_{4,1} strictly certifies and sharpens/matches (357/512, 359/512)", flush=True)
    log_lines.append("  [PASS] m=4 F_{4,1} strictly certifies and sharpens/matches (357/512, 359/512)")

    out_dir = Path(__file__).resolve().parent
    (out_dir / "residue_certificate_general_N512.log").write_text("\n".join(log_lines) + "\n", encoding="utf-8")
    (out_dir / "residue_certificate_general_N512.json").write_text(
        json.dumps({"grid": GRID, "finite_digits": FINITE_DIGITS, "scale": SCALE, "certificates": results}, indent=2),
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
