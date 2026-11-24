"""Check all 20000 terms of the OEIS A058651 b-file (continued fraction of pi+e) against a rigorous
Arb enclosure, and compute the size of the implied denominator bound (2026-11-24).

Classification (AGENTS.md): 文献核查与复现 (re-verifying published data) + 有限计算.

The common continued-fraction prefix of the two exact endpoints of an Arb enclosure of e+pi is
provably a prefix of the continued fraction of e+pi.  We compare it with the b-file (downloaded from
https://oeis.org/A058651/b058651.txt; not stored in the repo, its SHA-256 is printed) and compute
the number of digits of the convergent denominators q_{19998}, q_{19999} built from the b-file
terms.  If e+pi = p/q with this CF prefix, q >= q_{19999}'s size class -- the same kind of finite
exclusion as Proposition prop:denominator-bounds of paper 1, at a smaller scale.

Usage: python oeis_a058651_crosscheck_20261124.py PATH_TO_b058651.txt [DIGITS=25000]
"""
import hashlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rational_exclusion_bound_20261124 as R  # noqa: E402


def main():
    sys.set_int_max_str_digits(0)
    path = Path(sys.argv[1])
    digits = int(sys.argv[2]) if len(sys.argv) > 2 else 25000
    raw = path.read_bytes()
    terms = []
    for line in raw.decode("ascii").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        n, a = line.split()
        assert int(n) == len(terms), ("index gap", n)
        terms.append(int(a))
    lo, hi, _ = R.enclosure("epi_sum", digits)
    h, k, steps, prefix = R.simplest_rational(lo, hi, cf_record=10 ** 9)
    n_cmp = min(len(prefix), len(terms))
    first_bad = next((i for i in range(n_cmp) if prefix[i] != terms[i]), None)
    q_prev, q = 0, 1
    sizes = {}
    for i, a in enumerate(terms):
        q_prev, q = q, a * q + q_prev   # q is the denominator of [a_0; a_1..a_i]
        if i in (19998, 19999):
            sizes[i] = len(str(q))
    print(f"b-file sha256 {hashlib.sha256(raw).hexdigest()}  terms {len(terms)}")
    print(f"Arb enclosure: digits {digits}, rigorous common CF prefix length {len(prefix)}")
    print(f"compared {n_cmp} terms; first mismatch: {first_bad}")
    print(f"digits of q_19998 = {sizes.get(19998)}, q_19999 = {sizes.get(19999)} (from b-file terms)")
    ok = first_bad is None and n_cmp == len(terms) == 20000
    print("ALL 20000 B-FILE TERMS CONFIRMED" if ok else "NOT FULLY CONFIRMED")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
