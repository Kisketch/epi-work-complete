import EpiFormal.ResidueMultiAsymptotic
import Mathlib

/-!
# Paper-level interface: Paper 2C (windows, residues, and critical scaling)

**Paper**: *On window constraints, digit residues, and critical phase
transitions for modular continued fractions* --- split track **2C**
(`split/2C_windows_residues_finstate/`, 25 pp.; main paper A together with the
critical-scaling section).

**Which aspect / what content.**  This is the *continued-fraction window and
digit-residue side of the project*: exact Hausdorff dimensions of Hermite
window-count constraints (parity dimension 1; bounded/prescribed increments
dimension 1/2), short-window logarithmic frequency, eventual periodicity of
digit residues, the Lipschitz sandwich, the Bowen-free transfer-operator
dimension criterion, the certified `m ∈ {2,...,6}` brackets, the global strict
separation `dimH F_{m,m} < dimH F_{m,1} = dimH E_m`, the two-term expansion of
`dimH F_{m,r}`, and the multi-residue phase transition
`dimH F_{m,S,B} → max(1/2, s₀(S))` with three-term subcritical asymptotics and
supercritical rate `Θ(m^{-2s₀(S)})`.

**Section ↔ module map** (main manuscript L2884–4052):
- Dimensions of window constraints (L2884–3090): window modules (13 of them,
  `WindowMobiusCount.lean`, ..., `WindowShortAeRealize.lean`).
- Short windows / divergent counts (L3091–3340): `WindowBoundedUpper.lean`,
  `WindowCFBridge.lean`, `WindowShortAeRealize.lean`, `Audit.lean`.
- Eventual periodicity of digit residues (L3341–3657): `ResidueCertGenBase.lean`,
  `ResidueCertGenSound.lean`, `ResidueCertTable.lean`.
- Resolvent identity / strict separation / Fibonacci asymptotics (L3658–3794):
  `ResidueAsymptotic.lean`.
- Multi-residue phase transition (L3795–4052): `Ae.lean`, `Asymptotic.lean`,
  `Bridge.lean`, `Core.lean`, `Count.lean`, `Dim.lean`, `Discharge.lean`,
  `ModGeneral.lean`, `Prune.lean`, `Realize.lean`, `ResidueMultiAsymptotic.lean`,
  `Scale.lean`, `Table.lean`, `Thresh.lean`, `Upper.lean`.

**Status.**  All statements of this track are kernel-checked at Layer A with
only the three base axioms and zero `sorryAx`, **with two declared exceptions**:
(i) the strictness of the open intervals of the narrow certified brackets
(closed brackets are kernel-checked; open-interval strictness uses the cited
pressure formalism), and (ii) the critical-scaling layer, which is **not**
Lean-formalized: the pole decomposition
`C_S(p) = κ(S)/(p - 2s₀(S)) + O(1)` is proved in the paper text
(`sec-critical-scaling.tex`, Lemma `lem:pole`) and is imported here as the
explicit **project axiom** `C_S_pole_decomposition` (pragmatic path: the same
treatment as other declared external inputs; a long-term goal is to replace it
by an in-kernel proof via the spectral theory of the transfer operator).  The
scaling-limit theorem is proved in the text only; the algebraic identity
satisfied by the scaling function is proved in-kernel below
(`scaling_function_identity`).

**Axiom tiers in this module.**  Base axioms (`propext`, `Classical.choice`,
`Quot.sound`) plus exactly one project-added axiom (`C_S_pole_decomposition`).
`#print axioms` lines are the audit trail.
-/

open Filter Topology Set ResidueMultiAsymptotic

/-- **Pole decomposition of the structure series (project axiom, pragmatic
path).**  For every finite digit alphabet `S` with at least two positive
digits, the total continuant series `C_S(p) = ∑' n, W_S(p, n)` has a simple
pole at the critical exponent `2 * s₀(S)` with positive residue `κ(S)`:

`(p - 2 * s₀(S)) * C_S(p) → κ(S)` as `p → 2 * s₀(S)` from the right.

This is Lemma `lem:pole` of the critical-scaling section of the paper, proved
there from the Perron--Frobenius theorem for the transfer operator on
`A({|z - 1| < 1})` and Kato's analytic perturbation theory.  It is declared
here as an axiom so that downstream statements can be phrased and audited in
the kernel; replacing it by an in-kernel proof is a declared long-term goal.
See the module docstring for the axiom-tier classification. -/
axiom C_S_pole_decomposition (S : Finset ℕ) (hS1 : ∀ a ∈ S, 1 ≤ a)
    (hcard : 1 < S.card) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun p : ℝ => (p - 2 * poincareAbscissa S) * multiC S p)
        (𝓝[>] (2 * poincareAbscissa S)) (𝓝 κ)

/-- **Scaling-function identity (proved).**  The critical-window scaling
function `Φ(x) = (-x + √(x² + 4 d κ)) / 2` of the critical-scaling section is
positive and satisfies the exact quadratic identity `Φ * (Φ + x) = d * κ`
which defines it there.  This is the algebraic backbone of
Theorem `thm:critical-scaling`. -/
theorem scaling_function_identity (d κ x : ℝ) (hd : 0 < d) (hκ : 0 < κ) :
    0 < (-x + Real.sqrt (x ^ 2 + 4 * d * κ)) / 2 ∧
      ((-x + Real.sqrt (x ^ 2 + 4 * d * κ)) / 2) *
        ((-x + Real.sqrt (x ^ 2 + 4 * d * κ)) / 2 + x) = d * κ := by
  have h4 : 0 < 4 * d * κ := by positivity
  have hnn : 0 ≤ x ^ 2 + 4 * d * κ := by positivity
  set r : ℝ := Real.sqrt (x ^ 2 + 4 * d * κ) with hrdef
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : r ^ 2 = x ^ 2 + 4 * d * κ := Real.sq_sqrt hnn
  have hx2lt : x ^ 2 < r ^ 2 := by linarith
  have hr_gt : |x| < r := by
    have hlt : Real.sqrt (x ^ 2) < r := Real.sqrt_lt_sqrt (sq_nonneg x) (by linarith)
    rwa [Real.sqrt_sq_eq_abs] at hlt
  have h1 : x < r := (abs_lt.mp hr_gt).2
  constructor
  · have h2 : 0 < -x + r := by linarith
    linarith
  · have expand : ((-x + r) / 2) * ((-x + r) / 2 + x) = (r ^ 2 - x ^ 2) / 4 := by ring
    rw [expand, hsq]
    ring

/-- **Paper 2C, Theorem 42(ii) (multi-residue phase transition).**  For all
finite `S` and `B` with `d = |S| + |B| ≥ 1`, the Hausdorff dimension of the
multi-residue continued-fraction set converges to `max(1/2, s₀(S))`. -/
theorem paper2C_phase_transition {S B : Finset ℕ}
    (hS1 : ∀ a ∈ S, 1 ≤ a) (hd : 1 ≤ S.card + B.card) :
    Tendsto (fun m : ℕ => (dimH (multiResidueSet m S B)).toReal)
      atTop (nhds (max (1 / 2 : ℝ) (poincareAbscissa S))) :=
  ResidueMultiAsymptotic.tendsto_dimH_multiResidueSet hS1 hd

#print axioms scaling_function_identity
#print axioms paper2C_phase_transition
#print axioms C_S_pole_decomposition
