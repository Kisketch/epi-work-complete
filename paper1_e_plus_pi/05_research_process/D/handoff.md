# D 组交接（独立审稿 + Lean 核验）

代号 D。首轮任务：① 独立重建并机器核验命题 8.1；② 纸面审第二阶段定理 12。
两项均已完成，给出两个独立判定。

## 结论速览

| 任务 | 判定 | 层级 |
|------|------|------|
| 命题 8.1（prop:dirichlet-divisor） | **成立，整条命题 + 全部子引理机器验证** | 机器验证（Lean 内核，无 sorryAx、无项目公理） |
| 定理 12（thm:gauge） | **数学成立，无反例；三处隐含步骤需补写** | 纸面（未形式化，不能标机器验证） |

## 文件位置（均在 parallel_work/D/）

- `Prop81.lean` —— 命题 8.1 完整形式化，命名空间 `DVerify`，10 个声明。
- `axioms_output.txt` —— `lake env lean` 编译的公理审计原始输出（逐字，EXITCODE=0）。
- `report_prop81.md` —— 判定一：四声明拆分、量词/阈值/取整/整除方向核对、公理原文、复跑方法。
- `report_thm12.md` —— 判定二：三环节独立复核、可替换正文的修正 LaTeX 段落、形式化缺口清单。
- `handoff.md` —— 本文件。

## 命题 8.1 核验要点

- 验证方式：从 `epi_formal` 运行 `lake env lean <Prop81.lean 绝对路径>`，零写入，
  未 `lake build`/`lake update`，未动 `.lake` 缓存。退出码 0。
- 四声明全部机器验证：
  1. `dirichlet_witness`（见证存在，每个 j≥1）
  2. `linForm_identity`（整数线性形式恒等式）
  3. `linForm_abs_lt_one` / `linForm_eq_zero`（阈值 j>(3B/2)² 下 |N|<1 ⇒ N=0）
  4. `Psel_Qsel_coprime` / `divisor_restriction`（gcd(P,Q)=1 ⇒ q/gcd(q,B)∣d）
  组装：`prop_8_1_div`、`prop_8_1`。
- **1/(H+1) 无差异**：mathlib `Real.exists_int_int_abs_mul_sub_le` 上界恰为 1/(n+1)，
  与正文一致，直接引用，无需补证。
- **新增引理** `Psel_Qsel_coprime`：共享库只有 Q-Q 相邻互素，缺 P_j 与 Q_j 互素；
  用行列式 ±2 + P、Q 均奇补证。
- **不依赖 δ 公理**：`abs_deltaSel_lt` 在共享库已是定理（Hermite 积分路线），
  故本核验公理审计仅 propext/Classical.choice/Quot.sound。
- 未改阈值、量词、整除方向、除法口径；未增加假设。整除结论以 B(e+π)=A∈ℤ 为前提（条件性）。
- 比主稿多做的：把原「paper proof」命题升级为机器验证；补证共享库缺失的 gcd(P,Q)=1。

## 定理 12 审稿要点

- 三环节均通过独立复核，**未发现反例或失效公式**：
  1. 短区间 ↔ 缺陷前缀：常数略松但方向对；端点舍入歧义集可数。
  2. 次水平集 → 精确水平集正测度：依赖「严格次水平集 H^{h_k}-零」独立引理；
     须显式区分 {Λ≤k/4}（数字像所在）与 {Λ<k/4}（被移除的零测部分）。
  3. 稠密平移不变 ⇒ Lebesgue ⇒ 无穷：成立；需补 Borel 可测性推导与 σ-有限分支。
- 问题全是「正文未写明的隐含步骤」，非逻辑错误。report_thm12.md 给了可直接替换的
  修正 LaTeX 证明段落（补端点、严格/非严格区分、Borel、σ-有限）。
- 定理 12 维持纸面层：其依赖的分类定理、有限水平集维数定理已机器验证，
  但 gauge 构造/质量分布/稠密不变性本身未形式化。

## 验证状态

- 命题 8.1：**已机器验证**（内核 + 公理审计，原始输出在 axioms_output.txt）。
- 定理 12：**纸面审稿通过**，未形式化（首轮范围外）。

## 下一步（供总控/后续轮次）

1. 总控可把 report_prop81.md 的机器验证状态并入主稿 §sec:lean，
   将命题 8.1 从「paper proof」改标为「kernel-checked」，引用 DVerify.prop_8_1。
2. 总控可采纳 report_thm12.md 的修正 LaTeX 段落替换定理 12 证明，补齐三处隐含步骤。
3. 若要把定理 12 机器化，按 report_thm12.md 末尾的 5 项形式化缺口清单推进
   （可测性、严格次水平集零、质量分布、Haar 唯一性、σ-有限）。非首轮范围。
4. A 组（parallel_work/A）已在做 Dirichlet 窗口的见证分类与 π 无界性；
   D 的命题 8.1 整除引理可作为 A 的「有理性假设下商整除 B」的机器验证支撑。
   A 的 gcd 估计/无界性仍开放，D 未触碰。

## 诚实声明

e+π 无理性仍开放。命题 8.1 是必要条件（条件性整除限制），定理 12 是测度论 spin-off，
两者都不声称、也不暗示解决该开放问题。本核验未伪造任何证明，机器验证与纸面严格分层。
