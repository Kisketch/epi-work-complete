# Frostman 架构重设计（2026-11-21）：E2-Hinter/F1 路线退役，直接组装路线

## 一句总判断

E2（`frostman_of_count_thresh`，Hinter 接口）与 F1（`mass_distrib_of_diam_bound`，`∀ V` 逐集假设）两条路线**退出 windows 链**（文件保留、验证有效、审计条目保留，仅不再作为 L02/L05 的地基）；改走论文原文（L1027–1055、L2536–2557）的**逐窗选层直接组装**。

## 退役理由（两条，每条都已证实）

### R1：Hinter/`∀V` 在 `V = univ` 处空真，不可 discharge

- `Metric.diam univ = 0`（`ediam = ⊤`，`toReal ⊤ = 0`）。
- Hinter 对 `(V = fun _ => univ, F = {⋆})` 要求 `Kc/M ≥ 1` 且 `Kc/M ≤ 0^s = 0`（`s > 0`），不可能。
- F1 的 `(h : ∀ V, μ V ≤ ofReal (C * diam V ^ s))` 同理：`V = univ` 迫使 `μ univ = 0`，与 `hK : ofReal C ≤ μ K` + 单调性（`μ K ≤ μ univ`）矛盾（`0 < C` 时）。
- 结论：两定理本身验证通过（空真蕴含仍为真），但**没有任何合并且能 discharge 它们的接口**；继续在其上搭建等于在沙上盖楼。

### R2：单层 stopped 原子在数学上就不可能通过任意小窗阈值

- 固定 `M = N`（总原子数）时阈值要求 `((2D+3L)/d0+2)/N ≤ D^s`，`D → 0⁺` 时左端 → `(3L/d0+2)/N > 0`，右端 → 0，恒假。
- E2 的证明只在 S3 加厚子覆盖上实例化 Hinter（`diam ≥ 2ρ > 0`），但 ρ 可任意小，阈值仍无一致下界；模板靠**逐窗选层**（S5，`1/Q < diam`）+ 多层原子族绕开，单层 stopped 族无此自由度。

## 论文实际结构（tex 行号锚点，全部已实读）

- L1027–1029：覆盖集限制 `0 < h_i < Q_{N_s}^{-1}`（`δ`-限制；`diam = 0` 的单点集另行 `μ = 0`，因 `M_n^{-1} → 0`）。
- L1030–1034：逐窗选层 `Q_{n_i+1}^{-1} ≤ h_i < Q_{n_i}^{-1}`（单调趋零尺度 + Nat.find；即我们的 F3a `sandwich_of_tendsto`）。
- L1036–1044：交数 ≤ 3（格点间距论证；我们的 `meet_card_of_diam_le`/`window_overlap_le`）。
- L1015–1026：层阈值 `3/M_n ≤ Q_{n+1}^{-s}`（渐近比较；`eq:mass-scale-bound`）。
- L1047–1050：组装 `μ(U_i) ≤ 3/M_{n_i} ≤ Q_{n_i+1}^{-s} ≤ h_i^s`。
- L2536–2557（windows 自己的版本）：多层分裂质量界 `μ(I_j) ≤ exp(-bj log j + O(j))` + 窗交数 ≤ 17 + 对数比较 `log(h^{-1}) ≤ 2 log H_{j+1} = 2j log j + O(j)` + `O(h^s)`（`s < b/2`）。

## 修订路线（直接组装，T12 形状）

- 复用（已验证）：F3a 选层、meet_card 交数、child_len 柱径、coprime_count 计数、E2 的 S1–S4+S8–S9 骨架（复制，不 import E2 主定理）。
- 新建（按序）：多层分裂质量界（`∏ C_1 i^{-b}` 乘积界）→ 对数比较（`H_j ↔ j` 关系，需读论文 `H_j` 定义）→ 逐窗选层组装（S6/S7 形状）→ T12 形状主定理（S1–S4+S8–S9 + 新 S6/S7）。
- E2/F1 文件：不动（验证与审计有效）；本文件为 supersede 指令，L02/L05 不再引用二者主定理（T1/T10 通用引理仍可复用）。

## R3：全局 M 接口的不可行性证明（2026-11-21 补记）

E2（`frostman_of_count_thresh`，Hinter 接口）与 F1（`mass_distrib_of_diam_bound`，`∀V` 逐集假设）的退役理由已由 R1/R2 覆盖；本条补记**为什么任何保留全局 M 的修补都不可行**，从而锁定"逐窗选层直接组装"为唯一路线：

- `M` 必须同时满足 Hcount（`ΣKc/M ≥ 1`，倾向 M 小）与逐窗阈值（`Kc_i/M ≤ D_i^s`，倾向 M 大）；可行性要求 `ΣKc ≥ max_i Kc_i/D_i^s`，对任意小窗（`D_i → 0`）恒假。
- 模板的解法是**根本不要全局 M**：逐窗选层（S5，`1/Q < diam`），每窗阈值用本层常数（`2/M_{lvl}`），Hcount 经顶层总数 `M_N` 相消（S6c `le_of_mul_le_mul_left`）。
- 结论：L02/L05 必须走**逐窗选层直接组装**（S5+S6+S7 形状，无 Hinter、无 F1、无全局 M）。

## R4：Hinter 满足性修正 + discharge 规格（2026-11-21 补记二）

R1/R2 针对的是**手术前**的 Hinter（无正性前提）：`V = univ`（diam junk 0）与空集 `F = ∅`（`1 ≤ 0`）使其不可满足。E2 手术后 Hinter 含 hpos 前提（`Nonempty → 0 < diam`），反例被排除：
- `V = univ`：nonempty 但 diam = 0，违反 hpos → Hwin 无需处理。
- 空集：`Kc = ∅-filter = 0`，`0/M ≤ 0^s`（`s > 0`）成立。
- `F = ∅`：`K ⊆ ⋃∅ = ∅` 迫使 `K = ∅`；非空 K 下该分支前提为假。E2 定理本身对 `K = ∅` 空真成立，无矛盾。

剩余工作是纯 discharge（对非空 K），规格如下（Hwin 当前形状：`lvl/Kc + h_layer/h_meet/h_thresh + Hcount/Hthresh`，E2 证明只消费 Hcount/Hthresh）：
- 每窗选层：sandwich（F3a；需 `0 < D`（hpos 给）+ `D ≤ 1/H_j0²`（top-scale 接口 htop；`D > 1` 时改 trivial 分支：`Kc ≤ N_tot` + `1 ≤ D^s`）。
- 交数：meet_card（逐层原子族，不交内部 + 最小长度 + 有界窗）。
- 阈值：`Kc/M_N ≤ (1/Q)^s ≤ D^s`，经 fiber-upper（`hfib`）+ 层计数（`hMcount`，单调性）+ 对数比较（`logH` 接口）+ sandwich 下界 + `rpow` 单调。
- Hcount：top 双计数（top 原子 ⊆ K + K 被覆盖；`card_le_card_biUnion`），`M_N` 为顶层总数。
- 嵌套（子柱 Icc ⊆ 父柱 Icc）与 uniform-ish 纤维为显式接口（CF 理论后续工作，不阻塞 L05 组装文件的形状）。

## 待读（更新）

- ~~论文 `H_j` 定义与增长~~已读（见上）。
- P2 柱树已落地：`WindowWordTree`（均匀分支计数）、`WindowStoppedTree`（嵌套/不交/均分）、`WindowLevelCount`（多层下界）、`WindowDescFiber`（子孙归属/乘积界）、`WindowMassProd`（乘积闭合）——见各 merge 记录。
- P2 剩余：stopped 规则实例化（用方：coprime 计数 + `H_j` 定义 + 分支下界 `≫ j^b` discharge 接口）。
- 阈值蓝图子代理进行中（`ses_dfef6d91bffec3hwVNIxt6jpCb`；交付后对照本文档 S6/S7，不重复造）。
