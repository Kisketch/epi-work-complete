"""Emit ONE chunk (self-contained) of the N=512 certificate data for resource testing.

Usage: py -3.13 verification/emit_cert_chunk.py <chunk>   (chunk in 0..7)
Emits epi_formal/EpiFormal/ResidueCertChunk<N>_Draft.lean with rows [64c, 64c+64):
data slices + h_hi + hcert restricted to the chunk (global index statements).
"""
import sys
from pathlib import Path

import residue_certificate_general_N512 as cert

C = int(sys.argv[1]) if len(sys.argv) > 1 else 0
assert 0 <= C < 8
LO, HI = 64 * C, 64 * (C + 1)

M, R, S = 4, 1, cert.Fraction(179, 256)
rows, lower_tail, upper_tail, k_cut = cert.coefficients(M, R, S)
vector = cert.provisional_vector(rows, (lower_tail + upper_tail) // 2)
N, SCALE, K = cert.GRID, cert.SCALE, k_cut

srows = rows[LO:HI]
mat, maxvmat, cell_l, cell_r = [], [], [], []
for j, row in enumerate(srows):
    mrow, vrow, lrow, rrow = [], [], [], []
    for (lo, hi, left, right) in row:
        maxv = max(vector[left : right + 1])
        mrow.append(hi * maxv)
        vrow.append(maxv)
        lrow.append(left)
        rrow.append(right)
    mat.append(mrow)
    maxvmat.append(vrow)
    cell_l.append(lrow)
    cell_r.append(rrow)


def arr1(xs):
    return "#[" + ", ".join(str(int(x)) for x in xs) + "]"


def arr2(xss):
    return "#[" + ", ".join(arr1(r) for r in xss) + "]"


o = []
o.append("import Mathlib")
o.append("")
o.append("set_option maxHeartbeats 2000000")
o.append("set_option maxRecDepth 10000")
o.append("")
o.append("def get1 (a : Array Nat) (i : Nat) : Nat := a[i]!")
o.append("def get2 (a : Array (Array Nat)) (j k : Nat) : Nat := ((a[j]!)[k]!)")
o.append("")
o.append(f"def certVecC{C} : Array Nat := {arr1(vector)}")
o.append("")
o.append(f"def certHiC{C} : Array (Array Nat) := {arr2(mat)}")
o.append("")
o.append(f"def certMaxVC{C} : Array (Array Nat) := {arr2(maxvmat)}")
o.append("")
o.append(f"def certCellLC{C} : Array (Array Nat) := {arr2(cell_l)}")
o.append("")
o.append(f"def certCellRC{C} : Array (Array Nat) := {arr2(cell_r)}")
o.append("")
LOV, HIV = LO, HI
o.append(f"theorem cert_h_hi_c{C} : ∀ j ∈ Finset.range 512, ∀ k ∈ Finset.range 130,")
o.append("    ∀ i ∈ Finset.range 512,")
o.append(f"    {LOV} ≤ j → j < {HIV} →")
o.append(f"    get1 certCellLC{C} (j - {LOV}) k ≤ i → i ≤ get1 certCellRC{C} (j - {LOV}) k →")
o.append(f"    get1 certVecC{C} i ≤ get1 certMaxVC{C} (j - {LOV}) k := by")
o.append("  decide")
o.append("")
o.append(f"theorem cert_hcert_c{C} : ∀ j ∈ Finset.range 512, {LOV} ≤ j → j < {HIV} →")
o.append(f"    (Finset.range 130).sum (fun k => get1 certHiC{C} (j - {LOV}) k) +")
o.append(f"      {upper_tail} * get1 certVecC{C} 0 < 10000000000000 * get1 certVecC{C} j := by")
o.append("  decide")
o.append("")

dst = (Path(__file__).resolve().parent.parent / "epi_formal" / "EpiFormal"
       / f"ResidueCertChunk{C}_Draft.lean")
dst.write_text("\n".join(o) + "\n", encoding="utf-8")
print("wrote", dst, dst.stat().st_size, "bytes")
