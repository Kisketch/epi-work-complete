/-
  ResidueUpper358_DRAFT.lean — DRAFT, NOT TYPECHECKED.

  Status: proof skeleton only; pending `lake env lean` check AFTER the
  serial build completes AND ResidueRpowBridge_Draft + ResidueCertData41179_Draft
  check clean. Do NOT import from `EpiFormal.lean` / `Audit.lean` until checked
  (currently inert: no importer).

  Goal: dimH (residueConstSet 4 1) ≤ 179/256 = 358/512, strictly improving the
  analytic 4/5 bound, by instantiating `step_cert_upper_sound` with the N=512
  integer certificate data.

  Ingredients:
  - v, v_hi from certVec / certMaxV (pure vector majorants),
  - per-term power bounds from `enclose_rpow_upper` + emitted evidence,
  - row sums from `cert_hcert_data`, cell bounds from `cert_h_hi_maxV`,
  - cell-index correspondence `binOf = script cell` (general lemma, proved once),
  - tail bound from `enclose_rpow_upper` on the integral tail.
-/

import EpiFormal.TransferOperatorDim
import EpiFormal.ResidueCertData41179_Draft
import EpiFormal.ResidueRpowBridge_Draft

open Finset

/-- The exact rational upper bound proved here. -/
def s358 : ℝ := 179 / 256

/-- Cell-index correspondence: Lean `binOf` equals the script `cell` grid. -/
lemma binOf_eq_script_cell (N a e : ℕ) (hN : 1 ≤ N)
    (x : ℝ) (hx : x = 1 / ((a : ℝ) + (e : ℝ) / (N : ℝ))) :
    (TransferOperatorDim.binOf N hN x).val
      = min (N - 1) ((N * N) // (a * N + e)) := by
  sorry

/-- The test vector and step majorants, as nonnegative extended reals. -/
noncomputable def v358 : Fin 512 → ℝ≥0∞ :=
  fun j => ENNReal.ofReal ((certVec[j.val]! : ℝ) / 10000000000000)

noncomputable def vhi358 : Fin 512 → ℕ → ℝ≥0∞ :=
  fun j k => if k < 130 then
    ENNReal.ofReal ((certMaxV[j.val]![k]! : ℝ) / 10000000000000) else 0

/-- Main result (draft): the N=512 certificate closes at 179/256. -/
theorem dimH_residueMod4_le_179over256 :
    dimH (TransferOperatorDim.residueConstSet 4 1)
      ≤ ENNReal.ofReal (179 / 256 : ℝ) := by
  sorry
