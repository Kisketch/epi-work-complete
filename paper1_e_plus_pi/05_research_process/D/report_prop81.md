# D 组判定一：命题 8.1 机器核验状态

**结论：命题 8.1 成立，整条命题与全部子引理均已通过 Lean 内核检查，无 sorryAx、无项目公理。**

- 核验文件：`parallel_work/D/Prop81.lean`（命名空间 `DVerify`）
- 验证方式：从共享工程 `epi_formal` 运行 `lake env lean <绝对路径>`（零写入，未动 `.lake` 缓存、未 `lake build`/`lake update`）
- 编译退出码：**0**
- 工具链：Lean 4.35.0 / mathlib v4.35.0（与主稿 §sec:lean 一致）
- 公理审计原始输出：`parallel_work/D/axioms_output.txt`（逐字保留）

## 一、命题原文与量词

主稿 `prop:dirichlet-divisor`（第一阶段 tex 第 726–749 行）：

> 记 q=Q_j，P=P_j，H=⌊q√j⌋。若 B(e+π)=A（A∈ℤ，B 正整数），则对每个 j>(3B/2)²、
> 每对满足 1≤d≤H 且 |dπ−p|≤1/(H+1) 的整数 p,d，都有 q/gcd(q,B) ∣ d。
> 这样的整数对每个 j≥1 都存在。

量词核对（形式化逐字对应，未放宽）：
- 整除结论：**每个**合格见证 (p,d)（∀，不是 ∃）。形式化 `prop_8_1_div` 用 `∀ p d, 1≤d → d≤H → |dπ−p|≤1/(H+1) → …`。
- 见证存在：**每个 j≥1** 存在（∃）。形式化 `dirichlet_witness` 单列。
- 阈值：**严格** j>(3B/2)²。形式化用 `(3*(B:ℝ)/2)^2 < (j:ℝ)`，未改成 ≥ 或换常数。
- 前提：B(e+π)=A 为整数是**条件性假设**，整除结论依赖它；命题本身是必要条件，不声称证明 e+π 无理。

## 二、四个声明的拆分与完成情况

| # | 声明 | Lean 名 | 状态 |
|---|------|---------|------|
| 1 | Dirichlet 见证存在（每个 j≥1） | `dirichlet_witness` | ✅ 机器验证 |
| 2 | 假设有理 ⇒ 整数线性形式恒等式 | `linForm_identity` | ✅ 机器验证 |
| 3 | 阈值下 \|N\|<1，从而 N=0 | `linForm_abs_lt_one` / `linForm_eq_zero` | ✅ 机器验证 |
| 4 | gcd(P_j,Q_j)=1 ⇒ q/gcd(q,B) ∣ d | `Psel_Qsel_coprime` / `divisor_restriction` | ✅ 机器验证 |
| 组装 | 命题 8.1 整除部分 / 完整包装 | `prop_8_1_div` / `prop_8_1` | ✅ 机器验证 |

辅助：`H_pos`、`Qsel_pos_all`、`gcd_dvd_Qsel` 亦全部机器验证。

### 声明 1：见证存在性 —— 1/(H+1) 与 mathlib 完全一致，无需补证

任务书要求「若现成定理只给 1/H 而正文写 1/(H+1)，必须指出差异并补证」。
**核查结果：无差异。** mathlib `Real.exists_int_int_abs_mul_sub_le`
（`Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:94`）的陈述恰为

```
∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1)
```

上界就是 `1/(n+1)`，取 n=H_j 即得正文 `1/(H+1)`，直接引用，未补证、未改阈值。
（mathlib 该定理用 H+1 个分数部分 0,π,…,Hπ 的鸽笼/圆周间隙论证，与正文证明一致。）

### 声明 2：整数线性形式

N = A·Q_j·d − B·(P_j·d + p·Q_j) ∈ ℤ。恒等式（`linForm_identity`）：

  N = B·(d·δ_j + Q_j·(dπ−p))，其中 δ_j = Q_j·e − P_j。

代入 B(e+π)=A 后纯代数展开，`push_cast; ring` 闭合。

### 声明 3：阈值与严格小于 1

`linForm_abs_lt_one` 完整复现正文估计链：

  |N| ≤ B(d|δ_j| + Q_j|dπ−p|)
      < B(H/(2jq) + q/(H+1))
      ≤ B(1/(2√j) + 1/√j) = 3B/(2√j) < 1。

用到的输入：
- `abs_deltaSel_lt j`：|δ_j| < 1/(2j·Q_j)。**注意：共享库中此条已是定理**
  （EulerConvergents.lean 用 Hermite 积分表示证明，原公理已消除），故本核验不依赖任何 δ 公理。
- H ≤ q√j < H+1（`H_le`/`H_lt`，自然数向下取整 `Nat.floor_le`/`Nat.lt_floor_add_one`）。
- 阈值 (3B/2)² < j ⇒ 3B/2 < √j（`Real.lt_sqrt`）⇒ 3B/(2√j) < 1。

**取整核对**：H=⌊q√j⌋ 用 `Nat.floor`（ℕ 向下取整）。正文 H≤q√j<H+1 两个方向都用到，
形式化分别由 `H_le`、`H_lt` 提供，未用浮点。j>(3B/2)²≥9/4 蕴含 j≥1，故 `abs_deltaSel_lt`
的 j≥1 前提自动满足（`hj1` 显式推出）。

`linForm_eq_zero`：整数 |N|<1 ⇒ N=0（`abs_lt.mp` + `omega`）。

### 声明 4：互素与整除方向

**关键新增引理 `Psel_Qsel_coprime`：gcd(P_j,Q_j)=1。**
共享库只有相邻 Q-Q 互素（`Qsel_succ_coprime`），**没有** P_j 与 Q_j 互素。
本文件补证：由行列式 P_jQ_{j+1}−P_{j+1}Q_j=2(−1)^{j+1}（`sel_determinant`），
g=gcd(P_j,Q_j) 整除该行列式，故 g∣2；又 P_j、Q_j 均为奇数（`Psel_odd`/`Qsel_odd`），
g 不能为 2，故 g=1。

整除链（`divisor_restriction`），方向与正文一致：
1. N=0 ⇒ Q_j ∣ B·P_j·d（模 Q_j 消去 A·Q_j·d 项）。
2. gcd(P_j,Q_j)=1 ⇒ Q_j ∣ B·d（`Int.dvd_of_dvd_mul_left_of_gcd_one`）。
3. 令 g=gcd(Q_j,B)，则 gcd(Q_j/g, B/g)=1（`Int.gcd_div_gcd_div_gcd`），
   由 Q_j∣Bd 消去 g 得 (Q_j/g) ∣ (B/g)·d，再用互素消去得 **(Q_j/g) ∣ d**。

**整除方向核对**：结论是 q/gcd(q,B) ∣ d（商整除见证分母 d），不是 d ∣ 商，也不是 q ∣ d。
形式化 `(Qsel j / (Int.gcd (Qsel j) B : ℤ)) ∣ d` 与正文逐字一致。

**自然数/整数除法核对**：正文 q/gcd(q,B) 是精确商（gcd∣q）。形式化在 ℤ 上用 `Int.ediv`，
由 `Int.gcd_dvd_left` 保证 gcd∣q，故 `Int.ediv` 即精确商；`Int.ediv_mul_cancel` 用于
(Q_j/g)·g=Q_j、(B/g)·g=B 的还原。B 取 ℤ 且 0<B，与「B 正整数」等价，未引入 ℕ 截断除法歧义。

## 三、公理审计原始输出（逐字）

```
'DVerify.H_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.dirichlet_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.linForm_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.linForm_abs_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.linForm_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.Psel_Qsel_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.gcd_dvd_Qsel' depends on axioms: [propext, Quot.sound]
'DVerify.divisor_restriction' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.prop_8_1_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'DVerify.prop_8_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

仅三个 Lean 基础公理（propext、Classical.choice、Quot.sound）。
**无 sorryAx、无 admit、无 native_decide、无 e_transcendental/pi_transcendental/δ 公理。**
特别地，因 `abs_deltaSel_lt` 在共享库已是定理，本核验连经典 δ 估计都不依赖公理。

## 四、比现有稿件多核验了什么

- 主稿命题 8.1 原文标注「This proposition is a paper proof」（纸面证明）。
  本文件把它**升级为机器验证**：整条命题（存在性 + 每个见证的整除）首次过 Lean 内核。
- 新增并机器验证了共享库缺失的 `gcd(P_j,Q_j)=1`（此前只有 Q-Q 相邻互素）。
- 未增加任何假设：前提与主稿完全一致（B(e+π)=A∈ℤ，B 正整数，j>(3B/2)²，见证条件）。
- 未改变阈值、量词、整除方向或除法口径。

## 五、复跑方法

```
cd epi_formal
lake env lean "<绝对路径>/parallel_work/D/Prop81.lean"
```

退出码 0，stdout 即上述公理审计。文件自包含，仅 import Mathlib 与 EpiFormal.EulerConvergents。
