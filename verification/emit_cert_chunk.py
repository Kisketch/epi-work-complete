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


def emit_rows(tag, xss, C):
    """Emit one flat def per row plus a matrix def referencing them (shallow elaboration)."""
    names = []
    for i, r in enumerate(xss):
        nm = f"cert{tag}C{C}_r{i}"
        out.append(f"def {nm} : Array Nat := {arr1(r)}")
        names.append(nm)
    out.append(f"def cert{tag}C{C} : Array (Array Nat) := #[{', '.join(names)}]")
    out.append("")


out = []
out.append("import Mathlib")
out.append("")
out.append("set_option maxHeartbeats 2000000")
out.append("set_option maxRecDepth 10000")
out.append("")
out.append("def get1 (a : Array Nat) (i : Nat) : Nat := a[i]!")
out.append("def get2 (a : Array (Array Nat)) (j k : Nat) : Nat := ((a[j]!)[k]!)")
out.append("")
out.append(f"def certVecC{C} : Array Nat := {arr1(vector)}")
out.append("")
emit_rows("Hi", mat, C)
emit_rows("MaxV", maxvmat, C)
emit_rows("CellL", cell_l, C)
emit_rows("CellR", cell_r, C)
LOV, HIV = LO, HI
out.append(f"theorem cert_h_hi_c{C} : ∀ j ∈ Finset.range 512, ∀ k ∈ Finset.range 130,")
out.append("    ∀ i ∈ Finset.range 512,")
out.append(f"    {LOV} ≤ j → j < {HIV} →")
out.append(f"    get2 certCellLC{C} (j - {LOV}) k ≤ i → i ≤ get2 certCellRC{C} (j - {LOV}) k →")
out.append(f"    get1 certVecC{C} i ≤ get2 certMaxVC{C} (j - {LOV}) k := by")
out.append("  decide")
out.append("")
out.append(f"theorem cert_hcert_c{C} : ∀ j ∈ Finset.range 512, {LOV} ≤ j → j < {HIV} →")
out.append(f"    (Finset.range 130).sum (fun k => get2 certHiC{C} (j - {LOV}) k) +")
out.append(f"      {upper_tail} * get1 certVecC{C} 0 < 10000000000000 * get1 certVecC{C} j := by")
out.append("  decide")
out.append("")

dst = (Path(__file__).resolve().parent.parent / "epi_formal" / "EpiFormal"
       / f"ResidueCertChunk{C}_Draft.lean")
dst.write_text("\n".join(out) + "\n", encoding="utf-8")
print("wrote", dst, dst.stat().st_size, "bytes")
