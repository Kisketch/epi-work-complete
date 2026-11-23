"""Emit Lean certificate data for the (m=4, r=1) upper bound at s=179/256.

Reads NOTHING from disk except importing residue_certificate_general_N512
(deterministic: same floats, same lru_cache, same output as the committed run).
Emits epi_formal/EpiFormal/ResidueCertData41179_Draft.lean containing:
  - N0/K0/m0/r0/sNum/sDen/SCALE0/tailU literals,
  - vecData : Array Nat (512 entries),
  - hiData  : Array (Array Nat) (512 x 130 upper-bound numerators),
  - cellL/cellR : Array (Array Nat) (step-function cell ranges),
  - h_hi_data / hcert_data : single-`decide` obligations over Nats.
The emitted file is DRAFT (not imported anywhere); check with `lake env lean`
after the serial build completes.

Mapping to step_cert_upper_sound (see TransferOperatorDim.lean):
  v j        := (vecData[j]! : ENNReal) / SCALE  (cast via ofReal)
  v_hi j k   := (hiData[j]![k]! : ENNReal) / SCALE
  h_hi       follows from h_hi_data  (vector[i] <= M[j][k] on each cell)
  hcert row  follows from hcert_data (sums cleared of denominators)
"""

from fractions import Fraction
from pathlib import Path

import residue_certificate_general_N512 as cert

M, R, S = 4, 1, Fraction(179, 256)

rows, lower_tail, upper_tail, k_cut = cert.coefficients(M, R, S)
vector = cert.provisional_vector(rows, (lower_tail + upper_tail) // 2)

N = cert.GRID
SCALE = cert.SCALE
assert N == 512
K = k_cut
print(f"N={N} K={K} tail={upper_tail}")

# Recompute the exact per-cell upper numerators M[j][k] = hi * maxV,
# plus the pure vector majorants maxV (needed for v_hi in the assembly).
mat = []
maxvmat = []
cell_l = []
cell_r = []
for j, row in enumerate(rows):
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

# Sanity: re-derive the script margin from the dumped integers.
worst = None
for j, row in enumerate(rows):
    val = sum(m for m in mat[j])
    margin = Fraction(SCALE * vector[j] - val - upper_tail * vector[0],
                       SCALE * vector[j])
    if worst is None or margin < worst:
        worst = margin
print("recomputed worst upper margin:", worst, float(worst))
assert worst > 0


def arr1(xs):
    return "#[" + ", ".join(str(int(x)) for x in xs) + "]"


def arr2(xss):
    return "#[" + ", ".join(arr1(r) for r in xss) + "]"


out = []
out.append("/-")
out.append("  ResidueCertData41179_DRAFT.lean -- GENERATED, DO NOT EDIT BY HAND.")
out.append("  Generator: verification/emit_cert_data_41179.py (deterministic).")
out.append("  Source: N=512 integer certificate, m=4 r=1 upper side, s=179/256.")
out.append("  Status: DRAFT, NOT TYPECHECKED; pending `lake env lean` check.")
out.append("  Do NOT import from EpiFormal.lean / Audit.lean until checked.")
out.append("-/")
out.append("")
out.append("import Mathlib")
out.append("")
out.append("def certN0 : Nat := 512")
out.append(f"def certK0 : Nat := {K}")
out.append("def certM0 : Nat := 4")
out.append("def certR0 : Nat := 1")
out.append("def certSNum : Nat := 179")
out.append("def certSDen : Nat := 256")
out.append("def certSCALE : Nat := 10000000000000")
out.append(f"def certTailU : Nat := {upper_tail}")
out.append("")
out.append(f"def certVec : Array Nat := {arr1(vector)}")
out.append("")
out.append(f"def certHi : Array (Array Nat) := {arr2(mat)}")
out.append("")
out.append(f"def certMaxV : Array (Array Nat) := {arr2(maxvmat)}")
out.append("")
out.append(f"def certCellL : Array (Array Nat) := {arr2(cell_l)}")
out.append("")
out.append(f"def certCellR : Array (Array Nat) := {arr2(cell_r)}")
out.append("")
out.append("/-- Cellwise upper bounds hold on every cell (single decide). --/")
out.append("theorem cert_h_hi_data : ∀ j ∈ Finset.range 512, ∀ k ∈ Finset.range 130,")
out.append("    ∀ i ∈ Finset.range 512,")
out.append("    certCellL[j]![k]! ≤ i → i ≤ certCellR[j]![k]! →")
out.append("    certVec[i]! ≤ certHi[j]![k]! := by")
out.append("  decide")
out.append("")
out.append("/-- Every head row plus tail is strictly below the scaled test value. --/")
out.append("theorem cert_hcert_data : ∀ j ∈ Finset.range 512,")
out.append("    (Finset.range 130).sum (fun k => certHi[j]![k]!) +")
out.append("      certTailU * certVec[0]! < 10000000000000 * certVec[j]! := by")
out.append("  decide")
out.append("")

dst = (Path(__file__).resolve().parent.parent / "epi_formal" / "EpiFormal"
       / "ResidueCertData41179_Draft.lean")
dst.write_text("\n".join(out) + "\n", encoding="utf-8")
print("wrote", dst, dst.stat().st_size, "bytes")
