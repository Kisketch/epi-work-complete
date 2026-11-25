import EpiFormal.PolyGaugeAndPhaseTransition
import EpiFormal.GeneralGrowingDim
import EpiFormal.FiniteStateComplete
import Mathlib

/-!
# Paper-level interface: Paper 2B (general recurrence theory)

**Paper**: *On the general recurrence theory of weighted Diophantine
approximation: spectra, gauges, and dimension phase transitions* --- split
track **2B** (`split/2B_general_theory/`, 15 pp.; merged into main paper B
together with track 2A).

**Which aspect / what content.**  This is the *general-recurrence side of the
project*: for polynomial-growth recurrences $Q_{j+1}=(cj^r+d)Q_j+Q_{j-1}$ and
for arbitrary growing-quotient recurrences $Q_{j+1}=A_jQ_j+Q_{j-1}$
($A_j\to\infty$, including the convergent denominators of $e$ at $A_j=4j+2$),
it determines the full spectrum of the critical exponent, the zero-level
rank-2 lattice, the exact critical gauges with $1/r$-scaled logarithmic order,
the positive-level three-way splitting, and the dimension phase transition
$1-\alpha/r$ (polynomial case) / $(1-\tau)/(1+\tau\gamma_{\sup})$ with the
secondary supercritical transition at $\tau_{\mathrm{crit}}=1+1/\gamma_{\sup}$
(growing-quotient case), plus the finite-state-tail theorem whose critical
gauge base is the largest Perron root among marked components.

**Section ↔ module map** (main manuscript L1844–2881):
- Finite-state constraints on defect tails (L1844–1995): `Complete.lean`,
  `Gauge.lean`, `Positive.lean`, `Tail.lean`;
  `FiniteStateComplete.lean` (building on `FiniteStateGauge.lean`,
  `FiniteStateTail.lean`, `FiniteStatePositive.lean`).
- General polynomial-growth denominator recurrences (L1996–2542): `Discrete.lean`,
  `PolyGaugeAndPhaseTransition.lean`, `PolyWeightedLower.lean`,
  `PolyWeightedUpper.lean`, `TrichotomyAndPolyExtension.lean`.
- Universal extension to arbitrary growing-quotient recurrences (L2543–2881):
  `Dim.lean`, `Rec.lean` (`GeneralGrowingRec.lean`, `GeneralGrowingDim.lean`).

**Status.**  All statements of this track are kernel-checked at Layer A with
only the three base axioms (`propext`, `Classical.choice`, `Quot.sound`) and
zero `sorryAx`, **with one explicitly declared exception**: the
finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence
input of the finite-state tail theorem is passed as an explicit hypothesis and
is not derived inside the Lean kernel.  The `#print axioms` lines below are
the audit trail.
-/

open Filter Topology TrichotomyAndPolyExtension PolyGaugeAndPhaseTransition GeneralGrowingDim FiniteStateComplete
open scoped NNReal ENNReal

/-- **Paper 2B, polynomial-growth block: logarithmic asymptotics of `Q_n`.**
For every polynomial-growth recurrence `P`, `log Q_n = r n log n + O(n +
log n)`. -/
theorem paper2B_poly_log_Q (P : PolyRecData) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |Real.log (P.Q n : ℝ) -
        ((P.r : ℝ) * (n : ℝ) * Real.log (n : ℝ) +
          (Real.log (P.c : ℝ) - (P.r : ℝ)) * (n : ℝ))| ≤ C * Real.log (n : ℝ) :=
  poly_log_Q_asymptotic P

/-- **Paper 2B, growing-quotient block: exact subcritical dimension.**  For
`0 ≤ τ < 1` and finite level `t`, the weighted level set has Hausdorff
dimension `growTargetDim G τ` exactly. -/
theorem paper2B_grow_dimH_eq (G : GeneralGrowingRec.GrowingRecData) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    dimH (growWeightedLevelSet G τ t) = growTargetDim G τ :=
  dimH_growWeightedLevelSet_eq G hτ0 hτ1 ht

#print axioms paper2B_poly_log_Q
#print axioms paper2B_grow_dimH_eq
#print axioms FiniteStateComplete.mkMetric_graphTree_pos
