import EpiFormal.Classification
import EpiFormal.SpectralGap
import EpiFormal.FullSpectrumDiscrete
import EpiFormal.GaugeExact
import EpiFormal.TrichotomyAndPolyExtension
import Mathlib

/-!
# Paper-level interface: Paper 2A (core gauges and trichotomy)

**Paper**: *On the complete spectrum discretization and exact Hausdorff gauges
for the convergent denominators of $e$* --- split track **2A**
(`split/2A_core_gauge_trichotomy/`, 24 pp.).

**Which aspect / what content.**  This is the *metric theory of the selected
convergent denominators of $e$*: the complete discretization of the spectrum
$\Lambda(\mathbb R)=\frac14\mathbb Z_{\ge0}\cup\{\infty\}$, the rank-two
zero-level lattice $L=\mathbb Z+\mathbb Z\frac{e+1}{2}$, the exact Hausdorff
gauges $h_k(1/Q_n)=(2k+1)^{-n}$, the dimension-zero of every finite level, the
dimension-$1$ of the infinite level, the subcritical dimension $1-\alpha$, and
the three-way splitting of every positive level (limsup level, unsigned
exact-limit set with universal binary alphabet, signed exact-limit sets
collapsing to countable $L$-cosets).

**Section ↔ module map** (main manuscript L417–1843):
- Classification and initial spectral gap (L417–504): `Classification.lean`,
  `DeltaSign.lean`.
- Complete spectrum discretization (L505–621): `AeRealize.lean`, `Complete.lean`,
  `Dim.lean`, `Extension.lean`, `FullSpectrumDiscrete.lean`, `Gauge.lean`,
  `ModGeneral.lean`, `Positive.lean`, `SpectralGap.lean`.
- Finite level sets / infinite level (L622–853): `DimHCore.lean`,
  `DimHFinite.lean`, `GaugeExact.lean`.
- Subcritical weights (L854–1203): `QuarterPointFinal.lean`,
  `UnweightedCorrection.lean`, `WeightedDimHCore.lean`, `WeightedExactDim.lean`,
  `WeightedFiber.lean`, `WeightedFinal.lean`, `WeightedUpper.lean`.
- Critical levels / exact gauges / trichotomy (L1204–1843): `GaugeCircle.lean`,
  `GaugeExact.lean`, `GaugeLiminfComplete.lean`, `GaugeNull.lean`, `Circle.lean`,
  `Discrete.lean`, `TrichotomyAndPolyExtension.lean`.

**Status.**  Every statement of this track is kernel-checked at Layer A with
only the three base axioms (`propext`, `Classical.choice`, `Quot.sound`) and
zero `sorryAx`; no input of this paper lies outside the Lean kernel.  The
`#print axioms` lines below are the audit trail.  This file is a *paper-level
interface*: it restates one representative theorem per block and points to the
modules above; the full proofs live in those modules.
-/

open Filter Topology Classification FullSpectrumDiscrete GaugeExact TrichotomyAndPolyExtension

/-- **Paper 2A, Theorem 2 (classification).**  For the selected convergent
denominators `Qsel j` of `e`, `j ‖Q_j x‖ → 0` iff `x` lies in the rank-two
lattice `latticeL = ℤ + ℤ (e+1)/2`. -/
theorem paper2A_classification (x : ℝ) :
    Tendsto (fun j : ℕ => (j : ℝ) * distToNearestInt ((Qsel j : ℝ) * x)) atTop (nhds 0)
      ↔ x ∈ latticeL :=
  Classification.theorem2_classification x

#print axioms paper2A_classification
#print axioms SpectralGap.spectral_gap
#print axioms dimH_finiteLevel_zero
#print axioms signedExactLimitSet_pos_eq_coset
