import Mathlib

/-!
# 公理清单（审计用）

mathlib 尚未形式化的深层事实（使用前先查当前版本，若库中已有则替换公理为定理引用）。
这些公理仅用于验证论文推导，不构成对 e+π 无理性开放问题的证明。
审计方法：对每个定理运行 `#print axioms 定理名`，
输出中只允许出现本文件公理与 Lean 基础公理（propext、Quot.sound、Classical.choice）。
-/

/-- e 是超越数（Hermite, 1873）。 -/
axiom e_transcendental : Transcendental ℚ (Real.exp 1)

/-- π 是超越数（Lindemann, 1882）。 -/
axiom pi_transcendental : Transcendental ℚ Real.pi

/-- e 无理：由超越性推出（已证）。 -/
lemma e_irrational : Irrational (Real.exp 1) :=
  e_transcendental.irrational

/-- π 无理：由超越性推出（已证）。 -/
lemma pi_irrational : Irrational Real.pi :=
  pi_transcendental.irrational
