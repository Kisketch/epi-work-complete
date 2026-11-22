# 项目交接总纲（HANDOVER · 2026-11-18）

> **用途**：本文件是上下文压缩后的唯一权威入口。任何后续会话先读本文件即可无损接手，
> 无需回溯历史对话。所有路径为绝对路径。
> **纪律**：本项目全程执行「敌意审查协议」（见 §7），任何"已证"声明必须先过 Lean 内核 +
> `#print axioms` 无 sorryAx，并逐字贴出原始输出。

---

## 1. 一句话现状

$e+\pi$ 无理性**仍开放**（无已知工具，禁止空转或声称解决）。
项目本身已从"带缺口/带公理的半成品"变为**全链机器验证、无隐藏假设**的扎实成果：
T-finite 已坐实、两条 δ 公理已证明并物理删除、加权相变上界已证且纠正了原错误猜想。

---

## 2. 目录地图（整理后）

**项目根**：`C:\Users\Lgnatius\Documents\qwen-agent\QOTCWZPRRA\default\epi_work`

| 位置 | 内容 |
|---|---|
| `epi_formal\EpiFormal\*.lean` | 全部形式化模块（见 §4） |
| `epi_formal\Audit.lean` | 公理审计入口（`lake env lean Audit.lean`） |
| `epi_formal\PROOF_GAPS.md` | **缺口与进展登记（M1–M26），最重要的治理文档** |
| `epi_formal\LEMMA_AUDIT.md`、`FINAL_REVIEW.md`、`README.md` | 历史审计与说明 |
| `papers\` | 论文集中目录（两篇 tex/pdf + 数学证明文档 + 审查报告，见 §5） |
| `papers\archive\` | 历史版本（`paper_merged.tex` 等）与编译辅助文件 |
| `papers\numerics\` | 数值佐证脚本（非证明） |
| `.venv\Scripts\python.exe` | 数值用 Python（mpmath） |

**工作笔记（踩坑记录，写 Lean 前必读）**：
`C:\Users\Lgnatius\AppData\Local\Qianwen\User Data\qwen-agent-workspaces\runs\4bf3c2f8-9cc9-4f8b-aac2-954ac306f5c8\2026-11-16T07-13-12-409Z\build\NOTES_dimH.md`

---

## 3. 环境与命令（照抄可用）

- Lean 4.35.0 + mathlib v4.35.0；lake：`& "$env:USERPROFILE\.elan\bin\lake.exe"`
- **单文件零写入检查（优先用）**：
  `cd <项目根>\epi_formal; & "$env:USERPROFILE\.elan\bin\lake.exe" env lean <绝对路径>.lean`
- 单模块构建：`... lake.exe build EpiFormal.<模块名>`
- 全量：`... lake.exe build`（最近 9079 jobs 零错误）
- 审计：`... lake.exe env lean Audit.lean`（退出码 0，sorryAx 计数 0）
- PowerShell 5.1：**无 `&&` 用 `;`**；`<` 是保留符；**不要用 `2>&1`**（stderr 已分离）；
  长输出先 `| Out-File -Encoding utf8 x.log` 再 `Select-String` 读，避免刷屏。
- 数值：`<项目根>\.venv\Scripts\python.exe`；mpmath 精度 guard 300–500 位，
  容差用**绝对** 1e-100（相对容差在大 j 会比噪声还紧导致误报）。

---

## 4. 已机器验证的成果清单（全部仅 Lean 基础公理，除注明者）

### 4.1 第一阶段（e+π 相关，`paper.tex`）
- C1 Vieta 析取、C2 六配对至多一有理、C3 测度归约 μ(π)=2、
  C4 Meiburg Flint Hills 情形（原预印本公理已消除）、C5 Alekseyev 方向。
- C6 `Classification.theorem2_classification`：$j\|Q_jx\|\to0\iff x\in L=\mathbb Z+\mathbb Z\frac{e+1}2$
- C7 `Classification.corollary3_gap`：$x\notin L\Rightarrow\forall c<1/4$, ¬(最终 $j\|Q_jx\|\le c$)
- C8/C9 `EscapeReduction.reduction_to_lattice` / `P1_imp_irrational`（**换靶不降难**，P1 与原问题同族）

**以上 C6–C9 现已无条件**（δ 公理已删除，见 4.3）。

### 4.2 第二阶段（谱隙/维数，`phase2_paper.tex`）
- S1 `apprExponent_eq_zero_iff`、S2 `spectral_gap`（值域 ⊆ {0}∪[1/4,∞]）、
  S3 `levelSet_below_eq_lattice`、S4 `latticeL_countable`、S5 `dimH_levelSet_below`
- D1–D3 `DimHCore.Qsel_ge_factorial` / `Qsel_succ_le` / `fiber_card_le`
- **T-finite** `DimHFinite.dimH_levelSet_finite (c : ℝ) : dimH (levelSet (ofReal c)) = 0`
  （一切实数 c；原 AUDIT-GAP 的 4 个缺口全闭合）

### 4.3 δ 公理消除（OBL-5 **已彻底完成**）
`EulerConvergents.lean` 中两行 `axiom` 已替换为 `theorem`，证明内联自包含。
- `deltaSel_rec`、`cross_identity`（$Q_j\delta_{j+1}-Q_{j+1}\delta_j=2(-1)^{j+1}$）
- `namespace Hermite`：`I`/`E` 定义、初值、双递推、`E_eq_I`、`I_pos`、`sign_alternation`
- `abs_sum_eq_two`（$Q_j|\delta_{j+1}|+Q_{j+1}|\delta_j|=2$）
- **`theorem abs_deltaSel_lt`**、**`theorem deltaSel_tendsto_zero`**（原两条公理）

支撑模块：`PadeODE`（`padéR_ode`：$R_n+R_n'=p_n$）、`PadeDeriv`（`padéP_second_deriv`）、
`PadeBoundary`（四边界值零）、`PadeRecurrence`（`padeI_recurrence`）、`PadeIntegral`（FTC 表示）。

**打破循环依赖的关键**：删掉 `PadeIntegral.lean` 中未被使用的
`import EpiFormal.EulerConvergents`（该文件只用 padéR/padéP）。

### 4.4 加权相变（OBL-3 上界半，本轮新增）
- **`WeightedPhase.content_core_tendsto`**：$s>1-\alpha\Rightarrow K^n(n!)^{1-\alpha-s}\to0$
  （归约到 `DimHFinite.tendsto_powB_div_factorial_rpow`，$\beta=s-(1-\alpha)$）
- 上界定理 $\dim_H\{\Lambda_\alpha\le c\}\le1-\alpha$：纸面严格证明 + 上述解析核心机器验证；
  $\alpha=1$ 特例即 T-finite（全机器验证）。

### 4.5 项目剩余公理（仅 3 条经典事实，白名单内）
- `Axioms.lean`：`e_transcendental`（Hermite 1873）、`pi_transcendental`（Lindemann 1882）
- `Measure.lean`：`mu_e_eq_two`（μ(e)=2）

**δ 两条公理已不在此列。** 全项目 sorryAx = 0。

---

## 5. 论文与文档（整理后集中于 `epi_work\papers\`）

| 文件 | 说明 |
|---|---|
| `第一阶段_e_plus_pi.tex` / `.pdf` | 32 页。已证结果+归约链+障碍分析；**不声称解决中心问题** |
| `第二阶段_谱隙与维数.tex` / `.pdf` | 6 页。谱隙+T-finite（机器验证）+加权上界+修正后猜想 |
| `δ符号交替定理的严格数学证明.md` | Hermite 积分表示的完整分析证明（人类可读） |
| `加权相变上界定理.md` | $\dim_H\le1-\alpha$ 严格证明 + 纠正原猜想 |
| `两篇论文审查总结.md` | 七类攻击逐条审查结论 |
| `存量审计报告.md` | claim→依赖→判决全表 |
| `archive\paper_merged.tex` | 11-14 旧合并稿（历史保留，勿用于编译） |
| `numerics\spectral_numerics.py` | 数值佐证（**非证明**） |

两篇 tex **均自包含**（无 `\input`/`\includegraphics`/`\bibliography`），可独立编译。

---

## 6. 未闭合义务（OPEN）

| 编号 | 内容 | 性质 |
|---|---|---|
| **OBL-3a** | 一般 α 上界的完整 Lean 装配（分支引理 $B_j\le Kj^{1-\alpha}$ + 覆盖带 rpow） | 工程；解析核心已验证 |
| **OBL-3b** | 加权相变**下界** $\dim_H\ge1-\alpha$（需 Frostman 质量分布，存活树均匀分支） | **开放数学** |
| OBL-2 | $\Lambda=1/4$ 可达性（间隙是否开） | 开放，非必须 |
| OBL-4 | $e+\pi$ 无理性 | **开放，无已知工具，禁止空转** |
| OBL-1 | T-finite 组装 | **已闭合** |
| OBL-5 | δ 公理消除 | **已彻底完成（含物理删除）** |

**NEXT_PRIORITY 建议**：OBL-3b（真实数学方向）或 OBL-3a（把上界完全机器化）。

---

## 7. 敌意审查协议（全程生效，逐字要点）

- 首要义务是**不产生看起来像解法的噪声**；诚实 BLOCKED 严格优于含隐藏漏洞的证明。
- 禁止「显然/标准方法/例行公事/类似可证/由对称性」；每处展开为可检查子步骤或标 `[GAP]`。
- 断言接受依据：可追溯到前一步，或逐字陈述且假设逐一核验的定理。
- **不得自行标"已解决/证明完成"**；只产出候选证明提议审查。
- 每步后写「假设核验」段；未验证条件标 `[UNVERIFIED]`。
- 路线死掉输出 `ROUTE-DEAD` + 精确理由，不悄悄换路线。
- 输出四节：`## 存量审计` / `## 当前推进` / `## 自审结果` / `## 状态`
  （`VERDICT: PROGRESSING|PARTIAL|BLOCKED|ROUTE-DEAD`；`OPEN_OBLIGATIONS`；`NEXT_PRIORITY`）
- **七类攻击**：①步骤不推出（不等号方向/量词顺序）②假设未满足（援引定理条件逐一核验）
  ③小情形为假（n=2,3/退化）④同义反复（目标改头换面/偷引等价假设）
  ⑤证明过多（骨架套别的对象，若推出已知假或仍开放之事则找隐藏假设）
  ⑥错误解释（证了更弱/更易/不同读法的命题）⑦关键处手挥
- 自审：切独立对抗视角只依据写下的干净文本重读，再跑七类；全过标 `CLEAN-ONCE`（≠最终验证）。

---

## 8. 本轮（及前几轮）发现并修正的**真实错误**（审计轨迹，勿回退）

1. **假设错配**：`centerOf_mem_interv` 初版假设 $\|Q_jx\|\le\mathrm{rad}$，比水平集条件强 $Q_j$ 倍；
   改为 $j\|Q_jx\|\le t$。
2. **假命题分支**：`tailSet t 0 = ∅` 是假的（j=0 时 apprSeq=0≤t）；并集限制 J≥1。
3. **助理误判**："rad 与 apprSeq 差 $Q_j$ 倍、T-finite 是假命题"——算错（漏乘 $Q_j$），已撤回。
4. **论文错误叙事**：原称"无权重零集维数 1（Eggleston），权重降维到 0"——与自家分类定理矛盾
   （无权重零集 ⊆ L 可数、维数 0）。Eggleston 维数 1 针对**全体**收敛子分母，不适用稀疏子列。已改。
5. **原相变猜想错误**：原称"α<1 维数 1"——分支标度 $j^{1-\alpha}$ 迫使临界指数 $1-\alpha$。已改为
   上界 $\le1-\alpha$（已证）+ 下界猜想。
6. **第 5 类攻击误检验**：曾用 $q_n=n$ 检验并算错 $B_n$（应 $B_n\approx4t/n\to1$）；改用去权重检验。

**方法论教训（最重要）**：**内核验证 ≠ 叙事正确**。错误 4、5 都不在任何 Lean 声明里，
内核只检查定理、不检查论文解释文字是否与定理一致。定理与叙事必须**分别**做敌意审查。

---

## 9. 写 Lean 的高频踩坑（省时间，详见 NOTES_dimH.md）

- `ℝ≥0∞` 记号需 `open scoped ENNReal NNReal`；区间 `[[a,b]]`/`uIcc` 需 `open scoped Interval`
  （否则被解析成 List，报 `LocallyFiniteOrder ℝ` 合成失败）。
- **atTop on ℕ 无 CountableInterFilter 实例** ⇒ 禁用 `ENNReal.limsup_eq_zero_iff` 等；
  用 `Filter.limsup_le_iff`（ENNReal 值 autoParam 自动满足）、`eventually_lt_of_limsup_lt`。
- `eventually_of_forall` → v4.35 用 **`Filter.Eventually.of_forall`**。
- `natDegree_X_pow` 需**显式 n**；`X_pow_ne_zero` 不存在 → `pow_ne_zero n X_ne_zero`。
- `Polynomial.funext` + `intro t` + **完整 `simp`**（不要 `simp only` 列举，会漏常数多项式求值
  留下 `eval t 2`）+ `push_cast` + `ring`：这是证多项式恒等式的可靠套路。
- `ring` 在 `ℝ[X]` 里把每个 `C(...)` 当独立原子 ⇒ **降到 ℝ 逐点求值**再 ring。
- `C_neg`、`mul_assoc` 重结合（使 `derivative_C_mul` 能匹配）、`pow_succ` 统一指数、
  自然数减法先用 `omega` 证等式再 `rw`（否则模式不匹配）。
- `Function.iterate` 展开会留 `id`，需 `simp only [..., id_eq]`。
- `pos_of_mul_pos_left/right` 参数顺序易错 ⇒ 改用 `div_pos` + `mul_div_cancel_left₀` 最稳。
- 测度是 `ℝ≥0∞`，`linarith` 不适用 ⇒ 用 `lt_of_lt_of_le` + `norm_num`。
- `simp`/`field_simp` 常已闭合，多接 `ring`/`omega` 会报 "No goals to be solved"。
- 文档注释里的 `Λ`/`λ` 会被当绑定符 ⇒ 注释也用 ASCII（写 `Lam`）。

---

## 10. 诚实定位（不可动摇）

- $e+\pi$ 无理性开放；M17/M18 八路审计确认无工具。禁止声称解决。
- 谱隙现象**经典**（Lagrange 谱、Kraaikamp–Liardet 1991、BDS 2001、Moreira/Lima–Moreira）；
  覆盖论证是 Eggleston/BLR 型经典方法；Hermite 积分法是 1873 年经典手段。
  **新颖性只在具体实例签名**（e 选定子列 + 权重 j + 格 L + sharp 1/4）与**精确标度 $1-\alpha$**。
- **形式化 ≠ 新数学定理**；不得用 build jobs 数、声明数冒充数学进展。
- 预印本一律条件化标注（OpenAI μ(π)=2 未独立验证；Bertolin/Fischler–Rivoal 2026 未审核）。
- 数值（mpmath）**仅佐证**，永不参与证明。
