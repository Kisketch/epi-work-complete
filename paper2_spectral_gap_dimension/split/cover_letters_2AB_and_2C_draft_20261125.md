# Cover Letter Drafts for Paper 2 Two-Paper Split (`2A+2B` & `2C`)

> **使用与诚实口径说明（遵循 `AGENTS.md` 与 `.agents/rules/next-step-workflow.md`）**：
> 本文件提供经实库核对的两份英文 Cover Letter 草稿，严格避免夸大与错位：
> 1. 遵循「`2A + 2B` 合并主文 + `2C` 独立成篇」策略，**将 `thm:finite-state-tail` 准确置于 `2C`（不放入 `2A+2B`）**。
> 2. 与正文 `Verification scope` 完全一致：明确披露 `thm:finite-state-tail` 在 Lean 内显式传入 Perron–Frobenius 正右特征向量、`tab:residues-general` 的开区间严格性依赖外部 Bowen 压力形式主义（Lean 内核仅验证 $20$ 条闭界与 $5$ 条严格分离）、$s_0(S)=1/2$ 临界线收敛速率 / 超临界精确主导前因子常数 / `rem:fourth-term` 四阶猜想未证、以及 32 位 Chebyshev 配置数值仅为非严格佐证。
> 3. **投稿前必须由作者本人补填 `[Author name]`、`[Affiliation]`、`[Journal Name]`、`[Public Release Tag / Zenodo DOI URL]`、AI 使用政策合规声明及人工逐行审稿声明**，并将 `2A` 草稿中的 `Phase1`（未公开归档）引用替换为公开同伴/仓库引用后再正式投递。

---

## Template 1: Merged `2A + 2B` Main Manuscript

**Suggested venues**: *Journal of Number Theory*, *Acta Arithmetica*, *Ergodic Theory and Dynamical Systems*, or *Mathematika*  
**Prerequisite before sending**: Merge `2A` (`sec:class`, `sec:spectrum`, `sec:finite-levels`, `sec:weights`, `sec:gauge-core`) and `2B` (`sec:poly-rec`, `sec:growing-rec`), excluding `sec:finite-state-tail` (which belongs to `2C`).

```text
Date: [YYYY-MM-DD]

Dear Editors of [Journal Name],

Please consider our manuscript, "[Complete Spectrum Discretization, Exact Hausdorff Gauges, and Dimension Phase Transitions for Diophantine Approximation along Growing-Quotient Recurrences]," for publication in [Journal Name].

Motivated by—and beginning with—the selected convergent denominators (Q_j)_{j>=1} of e satisfying Q_{j+1} = (4j+2)Q_j + Q_{j-1}, this paper develops an unconditional metric Diophantine and fractal-dimension theory for weighted approximation along sparse, super-exponentially growing integer three-term recurrences Q_{j+1} = A_j Q_j + Q_{j-1} with A_j -> infinity. Our main contributions are:

1. Complete spectrum discretization and sharp three-way splitting for e-convergents: We prove that Lambda(x) = limsup_{j->infinity} j ||Q_j x|| has the completely discrete spectrum (1/4) Z_{>=0} union {infinity}, with zero-level set equal to the dense rank-2 lattice L = Z + Z((e+1)/2) and equidistant empty gaps (k/4, (k+1)/4). For every positive level k/4 (k >= 1), we establish a sharp trichotomy on both R and R/Z distinguishing the limsup level set (exact Hausdorff gauge h_k(1/Q_n) = (2k+1)^{-n}, yielding infinite sigma-finite measure), the unsigned exact limit set (universal critical gauge base 2 independent of k), and the signed exact limit sets (which each collapse to a single countable L-coset), together with an explicit liminf criterion covering oscillating gauges.

2. Coarse subcritical dimension and comparison with prior work: Every finite level set {Lambda <= c} has Hausdorff dimension 0, whereas for subcritical weights Lambda_alpha(x) = limsup_j j^alpha ||Q_j x|| (0 <= alpha < 1), both sublevel sets and admissible prescribed-limit sets have exact Hausdorff dimension 1 - alpha. While the unweighted case alpha = 0 agrees with Corollary 8 of Bugeaud, Liao, and Rams (2019), their Theorem 7 logarithmic growth hypothesis fails here because log Q_{j+1} / log Q_j -> 1, and related Cantor-series or exact-order frameworks (Cheng-Zhang, Baker-Ward, Tan-Tian-Wang-Wu) do not exhibit these discrete spectral gaps or signed-coset collapses.

3. Arbitrary growing-quotient recurrences and secondary supercritical phase transition: Extending beyond polynomial quotients (c j^r + d) to arbitrary integer recurrences Q_{j+1} = A_j Q_j + Q_{j-1} (A_j >= 2, A_j -> infinity), we establish the exact asymptotic identity matching the Kraaikamp-Liardet error normalization, complete spectrum Z_{>=0} union {infinity}, universal subcritical dimension distortion (1 - tau)/(1 + tau * gamma_sup) for 0 <= tau < 1 (where gamma_sup = limsup (log A_j)/(log Q_j)), and a secondary supercritical phase transition at tau_crit = 1 + 1/gamma_sup where finite sublevel sets collapse from the rank-2 fundamental-solution lattice L_G to the strict rank-1 rational sublattice (1/g)Z.

All theorems in the manuscript are proved by self-contained, traditional mathematical arguments. In addition, the main discretization, trichotomy, critical gauge, polynomial-growth, and growing-quotient theorems have been formally verified in Lean 4 (v4.35.0, Mathlib v4.35.0) using only Lean's three standard foundational axioms (propext, Classical.choice, Quot.sound) with zero sorry placeholders and zero custom project axioms. (This work grew out of Diophantine tools related to e + pi, but the irrationality of e + pi remains completely open and is not claimed here.)

[Insert journal-required AI-tool contribution statement and human proof-verification attestation.]

The source code, reproducibility scripts, and verification logs are archived at [Public Release Tag / Zenodo DOI URL]. This manuscript is original, has not been published previously, and is not under consideration elsewhere.

Sincerely,
[Author name]
[Affiliation]
[Email]
```

---

## Template 2: Standalone `2C` Manuscript (Windows, Modular Residues, Finite-State Tails & Certificates)

**Suggested venues**: *Journal of Number Theory*, *Ergodic Theory and Dynamical Systems*, or *Experimental Mathematics*

```text
Date: [YYYY-MM-DD]

Dear Editors of [Journal Name],

Please consider our manuscript, "[Continued-Fraction Windows, Finite-State Gauges, Global Residue-Class Separation, and Multi-Residue Asymptotics]," for publication in [Journal Name].

This paper investigates Hausdorff dimensions, critical gauges, and asymptotic expansions in two coupled continued-fraction settings—Hermite-type window counts on e-convergent scales (with finite-state tail restrictions on consecutive defects) and modular partial-quotient residue alphabets—pairing self-contained analytic proofs with machine-checked Lean 4 certificates. Our main results are:

1. Finite-state tail gauges and Hermite continued-fraction window laws: Extending the critical-gauge trichotomy to finite-state transitions on consecutive defects, we determine the exact Hausdorff gauge base as the largest Perron-Frobenius root among components supporting infinitely many extreme defects. On regular continued fractions, we establish the exact Hausdorff dimensions of Hermite window-count sets, prove the almost-everywhere logarithmic short-window lower bound with explicit constant (1 - e^{-1})/160, and prove full Hausdorff dimension 1 together with Lebesgue measure 0 for divergent-window sets.

2. Modular residue invariance and global strict separation for all moduli m >= 2: Using a uniform 24-Lipschitz sandwich and an unconditional transfer-operator dimension framework, we prove that eventual periodicity of partial quotients modulo m has the same Hausdorff dimension as the fixed residue alphabet F_{m,1} = E_m for every m >= 2, and enclose F_{m,r} to width 1/512 for 2 <= m <= 6 (e.g., F_{4,1} in (357/512, 179/256)). Introducing a closed-form metallic-continuant resolvent identity, we prove unconditionally that dim_H F_{m,m} < dim_H F_{m,1} = dim_H E_m holds strictly for every modulus m >= 2, together with exact two-term large-m asymptotics governed by C_r = sum_{k>=1} 1/q_k(r) and the reciprocal Fibonacci constant psi_Fib = sum_{k>=1} 1/F_k.

3. Multi-residue phase transitions, Euler-Mascheroni asymptotics, and fourth-term conjecture: Establishing a Bowen-free Poincare-abscissa dimension formula dim_H E_S = s_0(S) for finite alphabets S, we prove the global limit dim_H F_{m,S,B} -> max(1/2, s_0(S)), three-term subcritical asymptotics to O((log m)^2 / m^3) with explicit coefficient (1/2) d^2 C_S (gamma C_S - C_S') involving Euler's constant gamma, and two-sided supercritical power-law convergence Theta(m^{-2 s_0(S)}). We also formulate a heuristic scalar fourth-term conjecture (+(3/4) Gamma^3 (log m)^2 / m^3), clearly labeled as an open conjecture corroborated by symbolic expansion and 32-digit Chebyshev collocation (which also matches Brown's 2026 rigorous B-spline enclosure for E_{1,2} to all nine displayed digits).

4. Explicit positioning against recent 2025-2026 literature: Building on classical thermodynamic-formalism work of Hensley (1996, with its published erratum), Jenkinson-Pollicott (2018), and Chousionis-Leykekhman-Urbanski (2020), we explicitly distinguish our theorems from Chitanga-Lemmens-Nussbaum (Indag. Math. 2026), whose Corollary 1.2 settles the full dimension spectrum [0, dim_H F_{m,r}] for single arithmetic progressions but does not address uniform Lipschitz invariance across eventually periodic sets, global separation for all m >= 2, the constants C_r and gamma, or multi-residue phase transitions, and compare our integer-grid bounds with finite-element/B-spline methods of CLUW (2025) and Brown (2026).

5. Verification scope and transparent boundaries: All proofs in the manuscript are complete in traditional human-readable form. Independently, our main window, finite-state, resolvent, separation, and multi-residue theorems, together with the N = 512 transfer-operator table, have been checked in Lean 4 (v4.35.0, Mathlib v4.35.0) using only Lean's three standard base axioms (propext, Classical.choice, Quot.sound) and zero sorry placeholders (via Audit.lean, AuditResidueCert.lean [27 entries], and AuditResidueMultiAsymptotic.lean [24 entries]). For full transparency, we note that (a) the finite-state theorem takes the positive Perron-Frobenius right eigenvector as an explicit input; (b) Lean checks the 20 one-sided closed brackets and 5 strict separations at N = 512, while strict openness in the cited pressure comparison relies outside Lean on Bowen's formalism; and (c) the critical-boundary convergence rate at s_0(S) = 1/2, exact supercritical leading constant, and fourth-term conjecture remain unproved, while collocation numbers are clearly presented as non-rigorous numerical corroboration.

[Insert journal-required AI-tool contribution statement and human proof-verification attestation.]

The source files, scripts, and formal audit artifacts are available at [Public Release Tag / Zenodo DOI URL]. This manuscript is original, has not been published previously, and is not under consideration elsewhere.

Sincerely,
[Author name]
[Affiliation]
[Email]
```
