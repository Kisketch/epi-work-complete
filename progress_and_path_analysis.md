# e+π 无理性研究：完整工作记录、当前进度与全路径分析

**日期：2026-11-13｜性质：研究状态评估，非证明｜涵盖：云端九轮 + 本机执行全部已进行内容**

---

## 0. 一句话结论

**形式化侧（Lean）：论文的全部可形式化推导已机器验证，核心条件命题 H′ 无 sorryAx；仅余 T3（Alekseyev 方向）2 处真实缺口。**
**数学侧（开放问题本身）：e+π 无理性仍未证明，九轮研究 + 本机执行均未产生任何能判定它的新数学。四条经典路线的障碍同源于 e 与 π 缺乏结构连接，突破需要新范式。**

这两件事必须严格分开：形式化验证的是"论文推导的逻辑正确性"，不是"e+π 是否无理"。前者已完成大半，后者仍是世界未解之谜。

---

# 第一部分：论文本体

## 1.1 论文交付状态

- **文件**：`epi_work/paper.pdf`（英文主论文，已编译交付）。
- **标题**：*On the Irrationality of e+π: Proven Results, New Reductions, and a Systematic Obstruction Analysis*。
- **规格**：16 页，489849 字节，amsart 文档类，8 个正文章节 + 2 个附录。
- **编译质量**：零编译错误、零未解析引用、CJK 字符数=0（全英文，符合交付要求）。
- **修正**：档案原稿命题 3.8 的引号排版 bug（反引号方向错误破坏数学模式）已在 Windows 副本修正；档案原件未动。
- **源文件**：`epi_work/paper.tex`（744 行）。

## 1.2 论文章节内容清单（逐节）

| 章节 | 内容 | 对应已进行工作 |
|---|---|---|
| §1 Introduction | 问题陈述、贡献概述（九轮研究综合） | 全部 |
| §2 Preliminaries | 记号、无理性度量定义 | 第一轮引理1 |
| §3 Unconditional results | 定理2.1（至少一个超越）、定理2.2（四数至多一个有理）、e^π 超越、两个经典无理性证明（Fourier/Niven）、更强已知结果陈述 | M1/M2 形式化 |
| §4 New results | 定理A（度量归约）、定理B（连分数必要条件）、命题C（级数刚性）、命题D（四指数阻断）、定理E（μ₀=1+1/(M−1)）、命题G（℘ 缩放闭包）、命题H′（Flint Hills 桥） | 第一/二/三/四/六/七轮 + M3/M4/M5 |
| §5 Systematic attempts | 路线 A/B/C/D 障碍分析、四个桥梁恒等式候选、Mahler 分类 | 第一至四轮 |
| §6 Conditional frameworks | Schanuel 完整条件证明、Ax-Schanuel、Zilber、2026 motivic 前沿 | 第二/三/八轮 |
| §7 Computational verification | 符号机器验证、450 位区间证书、连分数实验、Flint Hills 数值、Chowla-Selberg（关闭） | 第二/三/四/六轮 + 本机复跑 |
| §8 Conclusion | 排除地图、存活靶点、开放问题、局限与饱和评估 | 全部 |
| 附录A Audit trail | 定理-来源-应用审计链 | 第九轮台账 |
| 附录B Reproducibility | 可复现性说明（脚本/环境） | 本机复跑 |

**论文诚实定位**：论文明确不声称证明 e+π 无理性；所有预印本依据条件化；交付的是"已证结果完整证明 + 新归约 + 系统障碍分析"。

---

# 第二部分：九轮研究全史（云端自主研究，全部已进行内容）

每轮均声明"未获得 e+π 无理性证明"。以下逐轮记录产出与判定。

## 第一轮：三个新严格结果 + 障碍地图奠基

- **定理 A（度量归约）**：若 e+π、e−π、eπ、e/π 任一有理，则 μ(π)=2。推论 A1：μ(π)>2 ⇒ 四数同时无理。把原问题归约到只涉及 π 的充分目标。
- **引理 1（度量不变性）**：μ(x+r)=μ(x)、μ(sx)=μ(x)、μ(1/x)=μ(x)（r 有理、s 非零有理）。→ 本机 M5 形式化。
- **引理 2**：μ(e)=2（Bundschuh）。→ 本机以公理 mu_e_eq_two 引入。
- **定理 B（连分数必要条件）**：若 e+π=p/q，则 π 的部分商序列是 e 的已知序列在某有限状态转换器（Raney 定理）下的像。补充：e+π∈(5,6) 非整数，q≥2。
- **命题 C（级数刚性）**：尾项 t_n=∑_{k>n}n!/k! 满足精确递推 t_{n+1}=(n+1)t_n−1。→ 本机 M4 形式化。
- **发散角度 D（乘法重构）**：e+π=r ⇒ e^e·e^π=e^r，元结论："e+π 有理"与现存全部超越定理相容，必须注入新信息源。
- **角度 E（积分桥梁）**：∫₀^π eˣsin x dx=(e^π+1)/2，产出 e^π（乘法型）。
- **角度 F（周期框架）**：π 是周期、e 是指数周期，概念图景（非定理）。
- **判定**：证明数 0；障碍地图五条路线全部定位。

## 第二轮：七方案逐个验证

- **命题 D（四指数阻断）**：e+π=r 假设下无法构造全代数 2×2 指数矩阵，四指数猜想标准应用路径阻断。
- **六指数定理**：至多一个值可控为代数，距应用条件极远，不足。
- **定理 E（新定量关系）**：μ(π) 上界 M 平移后给 e 的逼近指数 μ₀=1+1/(M−1)；M≥2 ⇒ μ₀≤2，与 μ(e)=2 完全相容，无矛盾。→ 本机 M3 mu0_identity 形式化。
- **Mahler 分类**：e、π、log2 均非 U 数，有理 Möbius 变换保持 Mahler 类，无分离。
- **最小未证假设层级**：Schanuel(1,iπ) ⟺ e,π 代数无关 ⇒ e+π 超越 ⇒ e+π 无理；无更便宜中间站。
- **420 位数值检验**：e+π∈(5,6)；e 连分数 1,2k,1 规律确认；{n!π} 窗口违反；递推误差 6.2×10⁻⁴¹⁹。→ verify_round2.py。
- **文献更新**：Bertolin arXiv:2609.15294（1-动机/Tannakian）、Powers arXiv:2508.12123（Hardy 方程攻克 γ+δ/e 的对比案例）。

## 第三轮：四方案落地 + 符号机器验证

- **Bertolin 精读 → 条件归约**：若 π=℘_Ω(代数点 p) 且 Bertolin 定理成立 ⇒ e,π 代数无关 ⇒ e+π 超越。子问题"π=℘(代数点)?"不弱于原问题。
- **三个桥梁候选全部排除**：Gauss 积分（π=4I²，二次摧毁线性）、Stirling（渐近非精确）、混合积分（产出 e^π）。
- **sympy 12/12 PASS**：Vieta、六配对、定理E、命题C、Gauss/混合/Stirling 积分。→ verify_round3.py。
- **Bai 2026 跟踪**：μ(π)≤7.101862832357（arXiv:2609.11276），代入定理E 得 μ₀≈1.1639≤2，无矛盾，关闭。
- **Lean 环境受阻**（云端无 Lean），记录路线图。→ 本机后续完成。

## 第四轮：命题 G + 首个严格区间证书

- **命题 G（℘ 缩放闭包）**：S={℘_Ω(p)} 对非零代数乘法封闭；"π∈S?"等价于周期与 ℘ 值的代数系数线性关系。文献确认无已知部分结果。
- **第四桥梁候选**：∫₀^∞ cos x/(1+x²)dx=π/(2e)，乘法型，排除。
- **机制总结论**：全部已知 e–π 联系（欧拉、e^π、coth、模形式、Gauss、Stirling、混合、cos 积分）生成机制同一——在周期处求指数值，产出全是 e^π 家族；e=e¹ 是代数点指数值，无已知恒等式加法连接两者。
- **450 位区间证书**：e+π 包围宽度<9.12×10⁻⁴⁵¹；分母 q≤1000 全排除；窗口违反 n=2,4,7..60。→ verify_round4.py + certificate_round4.json。
- **饱和评估**：初等/经典选项基本穷尽，剩余存活选项全在未证猜想层。

## 第五轮：档案合并

- 把四轮笔记与研究报告合并为累计研究档案（中文合并版），含完整排除板与全部证书。

## 第六轮：命题 H（Flint Hills 桥）+ Chowla-Selberg

- **命题 H（新条件命题）**：e+π 有理 ⇒ Flint Hills 收敛；逆否：Flint Hills 发散 ⇒ 四数无理。（第七轮更正归属为 Meiburg。）
- **π∈S 文献深挖**：Schneider 定理（S 元素全超越，无分离）；Huber–Wüstholz（1-周期线性关系已解决、代数关系未解决，子问题恰在边界外侧）。
- **Chowla–Selberg 路径关闭**：ϖ=Γ(1/4)²/(2√(2π))，π=Γ(1/4)⁴/(8ϖ²)，代入恒等循环，无新约束。120 位验证误差 7.7×10⁻¹²¹。
- **三计算实验**：Chowla-Selberg；定理B 机制可视化（CF 匹配位置1–2 即分歧）；Flint Hills S(10000)=30.31451083，最大项 n=355（355/113 收敛子分子），sin355=−3.014×10⁻⁵。→ verify_round6.py。

## 第七轮：自我更正（核验纪律的关键实例）

- **Alekseyev 原文精读**：定理5 对 (3,2) 阈值=2，空洞；只有"收敛⇒μ≤2.5"（推论4）非平凡。"μ<2.5⇒收敛"**不在** Alekseyev 论文。
- **正式更正命题 H → H′**：第二支柱真实来源是 Meiburg arXiv:2208.13356（预印本），命题下调为条件性。Wikipedia 把两来源混述导致第六轮误引。
- **formal-conjectures 对接**：issue #3484（2026-03-17 关闭，可行性 1/5），Flint Hills 陈述已入库。→ 本机 FlintHills.lean T3。
- **文献环境警示**：2026 OpenAI 批量论文含未核实 μ(π)=2 声称；本研究"不声称 μ(π)=2、逐条标注预印本"纪律正确必要。

## 第八轮：Meiburg 证明结构核验

- **Meiburg 全文精读**：第一层稀疏性引理（差商反证，Qₙ=Ω(n^{1/(1−ε₂)})）；第二层精细划分（S₁/S₂/S₃ 三分划，线性函数 f(μ)=1+u/v−μ）。弱阈值代数复核（(3+√3)/2≈2.366）。
- **可信度上调**：从"未知预印本"→"结构已核验的高可信预印本"，同行评审状态不变，公理标注保留。
- **Dan 2026 评估**（arXiv:2609.12338）：广义 Flint Hills 的 Hausdorff 维数 refinement，明确"经典 Flint Hills 仍未判定"，旁证非突破。
- **FlintHills.lean 骨架**：FlintHillsConjecture、alekseyev_bound（sorry）、meiburg_criterion（公理）、proposition_H'（完整接线）、flint_hills_diverges_bound。

## 第九轮：全量留痕 + Meiburg 补完核验

- **Meiburg 精细划分补完**：f(μ) 独立重算确认 1+u/v−μ（f′ 排版乱码不采信）；重数界定步压缩但逻辑完整；边界构造定理3.1（Sondow 公式）。主定理证明结构全部核验完毕。
- **定理审计台账**：50 项六组登记（A 超越经典18、B 丢番图9、C Flint Hills链10、D 分析恒等式8、E 自推13、F 核验纪律），每项含精确陈述/来源/核验方式/状态/运用位置。
- **状态**：e+π 未证；H′ 条件成立且支柱完整核验；四靶点"预期为假但未证伪"。

## 九轮累计排除板（完整）

| 路线/框架 | 状态 | 障碍坐标 |
|---|---|---|
| 级数/整数序列（A） | 阻断 | {n!π} 分布未知 |
| Niven 积分（B） | 阻断 | 无在 e+π 取零且导数受控的核 |
| 超越数论（C） | 阻断 | e^{iS}=−e^{ie} 落在所有定理外 |
| 丢番图逼近（D） | 阻断 | 三角界恒≥2，需 μ(π)>2（未知） |
| 连分数（定理B） | 阻断 | π 部分商无结构定理 |
| 四指数/六指数 | 阻断 | 命题D 构造性论证 |
| μ(π) 平移（定理E） | 自洽无矛盾 | μ₀=1+1/(M−1)≤2 |
| Mahler 分类 | 无分离 | e,π 同属非U |
| 桥梁恒等式（4候选） | 全排除 | 一切已知桥经由 e^π |
| Schanuel/Ax/Zilber | 悬于未证猜想 | 最小假设=Schanuel(1,iπ) |
| motivic（Bertolin） | 归约开放子问题 | π∈S?（预期否） |
| Chowla-Selberg | 循环关闭 | 无独立新元素 |

---

# 第三部分：本机执行全记录（Windows 侧，全部已进行内容）

## 3.1 环境部署

- **VM GUI 尝试（失败，已放弃）**：SendInput 点击/按键有 ~150% DPI 缩放偏移（宿主 1707×1067 @144DPI），键盘事件即使 Ctrl+G 抓取也不达guest。改用命令通道。
- **VM 命令通道**：vmrun 需guest密码（不可用）；共享文件夹 RM/RM-PRO（guest 挂载 /mnt/hgfs/RM）；VM IP 192.168.245.129，SSH 22 开放无免密。写 vm-setup.sh 由用户在 VM 自跑；Linux 侧由 Claude 负责。
- **Windows 原生工具链**：MiKTeX（pdflatex/xelatex/latexmk/biber）、git、uv、Strawberry Perl（winget 装，latexmk 依赖）、Python 3.12.14 venv（sympy 1.14.0 + mpmath 1.3.0）。
- **Lean 工具链**：elan（GitHub API 取 asset，elan-init.exe 直链返回 Not Found 的坑）+ Lean 4.35.0 + mathlib v4.35.0。mathlib git clone 超时 → codeload tarball 下载（无 byte-range，不能续传，整包重下 + tar -tzf 校验）。

## 3.2 论文编译

- pdflatex/latexmk 编译 paper.tex → paper.pdf（16页）。
- 修正 line 439 引号 bug（反引号方向破坏数学模式 → Missing $ inserted）。
- 核验：零错误、零未解析引用、CJK=0。

## 3.3 验证脚本复跑（全部匹配档案）

| 脚本 | 结果 |
|---|---|
| verify_round3 | 符号 12/12 PASS |
| verify_round4 | 450 位证书，分母≤1000 全排除，窗口违例 n=[2,4,7..60] |
| verify_round2 | 递推误差 6.2×10⁻⁴¹⁹ |
| verify_round6 | Chowla-Selberg 误差 7.7×10⁻¹²¹；S(10000)=30.31451083，最大项 n=355 |

## 3.4 Lean 形式化里程碑（M0–M5 全部完成）

- **M0**：lake 项目 epi_formal，lakefile 加 `globs=["EpiFormal.+"]`（否则子文件静默不编译）。
- **M1**：vieta_identity（by ring）。
- **M2**：quadratic_roots_algebraic（多轮迭代：放弃子代数塔超时路线→纯 ℝ 环运算；修正负判别式分支数学错误，实根强制 D=(S−2x)²≥0）；定理2.1/2.2、六配对。
- **M3**：mu0_identity（定理E）。
- **M4**：tail_summable / tail_recurrence（命题C）。
- **M5**：irrMeasure 定义修正（ℚ分子退化→ℤ分子+ENNReal）；neg/add_rat/mul_rat/inv 全证；const_absorption(_nn)、apprPairs_denom_unbounded/num_unbounded、mul_nat_le(_rev)/eq、add_rat_le；定理A sum/diff/quot/prod 全证。
- **Flint Hills 桥**：proposition_H' 无 sorryAx；flint_hills_term_tendsto_zero、flint_hills_diverges_bound 已证。

## 3.5 本轮（第十轮）T3 探索与障碍发现

- 尝试 alekseyev_diophantine，连续多轮 tactic 失败后核对数学，发现**分子分母障碍**（详见第五部分 F1）。
- 回退错误证明为干净 sorry，保留陈述，治理文件留痕。
- 出具本进度与路径分析报告。

## 3.6 治理文件（全部更新为最终真实状态）

PROOF_PLAN / RESEARCH_LOG / LEMMA_AUDIT / PROOF_GAPS / FINAL_REVIEW，含失败路线留痕与公理审计表。

---

# 第四部分：当前进度（精确状态）

## 4.1 Lean 公理审计（16 定理全部无 sorryAx）

全项目 `lake build` **9053 jobs 零错误**。

| 里程碑 | 定理 | 公理依赖 | 状态 |
|---|---|---|---|
| M1 | vieta_identity | Lean 基础 | ✅ |
| M2 | quadratic_roots_algebraic | Lean 基础 | ✅ |
| M2 | at_least_one_transcendental（定理2.1） | e_transcendental | ✅ |
| M2 | four_numbers_at_most_one_rational（定理2.2） | e_transcendental, pi_transcendental | ✅ |
| M3 | mu0_identity（定理E） | Lean 基础 | ✅ |
| M4 | tail_summable / tail_recurrence（命题C） | Lean 基础 | ✅ |
| M5 | irrMeasure_neg / add_rat / mul_rat / inv | Lean 基础 | ✅ |
| M5 | theoremA_sum / diff / quot | mu_e_eq_two | ✅ |
| M5 | theoremA_prod | e_transcendental, mu_e_eq_two | ✅ |
| 桥 | **proposition_H′** | **meiburg_criterion, mu_e_eq_two** | ✅ **无 sorryAx** |
| T3 | flint_hills_term_tendsto_zero | Lean 基础 | ✅ |
| T3 | flint_hills_diverges_bound | meiburg_criterion | ✅ |

## 4.2 剩余缺口（仅 2 处，均属 T3）

| 缺口 | 陈述 | 难点 |
|---|---|---|
| alekseyev_diophantine | 通项→0 ⇒ 最终 \|π−m/n\|≥n^(−(5/2+ε)) | 分子分母障碍（见 F1） |
| alekseyev_bound | Flint Hills 收敛 ⇒ μ(π)≤5/2 | 依赖前者 + ε-吸收 |

meiburg_criterion 以**公理**引入（预印本，证明结构第八九轮已完整人工核验，非内核、未同行评审）。

## 4.3 三个可信度层次（严格区分）

1. **机器验证**（Lean 内核+公理审计）：16 定理属此层，最高可信度。
2. **人工核验的预印本证明结构**：Meiburg 主定理已逐段核验，但以公理引入，非内核。
3. **符号/数值辅助**：sympy 12/12、450 位证书，旁证非证明。

**e+π 无理性本身不属任何一层——开放问题，本项目未证明。**

---

# 第五部分：形式化侧路径分析（可执行，按可行性排序）

## F1：补完 T3 Alekseyev 方向【最可行，纯形式化】★★★

**本轮发现的精确障碍（数学错误，非 tactic）**：
- sin 下界 |sin n|≤|n−mπ|；正确恒等式 **|n−mπ|=|m|·|π−n/m|**（n 分子、m 分母）。
- 但引理陈述与 irrMeasure 定义用 **n 作分母** 的 |π−m/n|。
- 错误写法 |n−mπ|=n|π−m/n| 不成立；field_simp;ring 残骸 `↑n−↑m·π=−(↑n·π)+↑m` 即证据。

**正确路线（三步）**：
1. 分子版引理：|π−n/m|≥|m|^(−(5/2+ε))，处理 n≍mπ 同阶替换（n³→m³）。
2. 分母无界双射换算到分母版（复用 apprPairs_denom_unbounded / const_absorption）。
3. 接 irrMeasure_le_of_eps 得 μ(π)≤5/2。

**可行性**：高。所需 machinery 全部已证可复用，无新数学风险。

## F2：Meiburg 公理→定理【可行但繁重】★★

证明稀疏性引理（差商反证）+ 精细划分（线性函数 f）。结构已核验，工程量大。价值：H′ 公理依赖从 2 降到 1。

## F3：μ(e)=2 公理→定理【可行，经典】★★

Bundschuh 经典结果，连分数 machinery。价值：定理A 仅依赖 e/π 超越公理。

## F4：e/π 超越性形式化【极繁重，长期】★

Hermite/Lindemann 完整形式化，mathlib 尚无。投入产出比低。

**关键认识**：F1–F4 全是"把已确立数学搬进 Lean"，**没有任何一条能证明 e+π 无理性**。

---

# 第六部分：数学侧路径分析（攻开放问题，全部未成功）

## 6.1 路线 A：级数法 → {n!π} 分布未知

命题4.1：e+π 有理 ⇒ 1−1/n<{n!π}<1。障碍：{n!π} 分布完全未知。π 无阶乘清分母级数。与 arXiv:2606.17303（2026 尾项判据 no-go）一致。

## 6.2 路线 B：Niven 积分 → 无受控核

端点导数整值性对任何有理端点成立；但 sin(e+π)=−sin e，sin e=0 ⟺ e/π 整数（未知），边界项不能消去。改造核引入 (1+e/π)² 幂，整值性崩塌。

## 6.3 路线 C：超越数论 → 桥梁落在定理外

e^{iS}=−e^{ie}：左超越右无信息。Baker 框架缺 e 的对数表示（e=log α ⟺ e^e 代数，开放）。个体超越性推不出和的无理性（π+(1−π)=1）。

## 6.4 路线 D：丢番图逼近 → 需 μ(π)>2

组合逼近三角界 d_n/b_n+b_n/d_n≥2 恒不趋于0。μ(e)=2 关闭 e 侧；μ(π)>2 未知（最新上界 Bai 2026 的 7.101862832357）。

## 6.5 共同障碍

**e 与 π 缺乏任何已知结构连接**。自 1996 Nesterenko 以来无实质突破。

## 6.6 条件性框架（全部悬于未证猜想）

- **Schanuel**：唯一够用，完整推导链已验证，但猜想本身未证（仅 n=1 成立）。
- **Ax-Schanuel**：函数域版本，不直接等价数值域。
- **Zilber**：同构问题开放，复指数非 o-极小。
- **四指数**：信息量不足。
- **Nesterenko**：涉及 e^π 而非 e。
- **Bertolin motivic**：归约 π∈S?（预期否，开放）。

## 6.7 靶点清单（认识论状态）

| 靶点 | 条件 | 状态 |
|---|---|---|
| μ(π)>2 ⇒ 四数无理 | 无条件 | 预期为假，未证伪 |
| Flint Hills 发散 ⇒ 四数无理 | Meiburg（已核验） | 预期为假，未证伪 |
| π∈S + Bertolin ⇒ e+π 超越 | 预印本 | 预期为假，未证伪 |
| 全新精确加法恒等式 | — | 无候选 |

**本机第十轮对靶点4探索**：e+π=1+∫₀¹eˣdx+∫₀¹4/(1+x²)dx（sympy 确认），但无清分母机制，blocked。

---

# 第七部分：文献陷阱与核验纪律

- **Carella arXiv:1706.08394（eπ 无理）**：未接受，D'Aurizio 评"looks very fishy"。
- **Carella arXiv:1902.08817（μ(π)=2）**：未接受。
- **openai/math "irrationality exponent of pi is 2"（2026-09）**：来源异常，未核验，不采信。
- **Hardy–Wright 中文版翻译错误**：误把 eπ 移入"已证无理"、删除 e+π，须对照英文原版。
- **纪律**：预印本条件化、乱码独立重算、弱来源标注、未登记不使用、数值非内核。

---

# 第八部分：完整产物清单（全部已交付/已生成）

## 8.1 论文
- `epi_work/paper.pdf`（16页英文主论文，已交付）
- `epi_work/paper.tex`（源文件）

## 8.2 Lean 形式化（epi_work/epi_formal/）
- `EpiFormal/Axioms.lean`（e/π 超越公理 + 无理性推论）
- `EpiFormal/Elementary.lean`（M1/M2）
- `EpiFormal/Measure.lean`（M3/M5，~980行，零 sorry）
- `EpiFormal/Series.lean`（M4）
- `EpiFormal/FlintHills.lean`（桥 + T3，2 sorry）
- `Audit.lean`（公理审计）
- `lakefile.toml`（globs 配置）

## 8.3 验证脚本与证书（epi_work/verify/）
- verify_round2/3/4/6.py（复跑匹配档案）
- certificate_round4.json（450位区间证书）

## 8.4 治理文件（epi_work/epi_formal/）
- PROOF_PLAN / RESEARCH_LOG / LEMMA_AUDIT / PROOF_GAPS / FINAL_REVIEW

## 8.5 本报告
- `epi_work/进度与路径分析.md`（本文件）

## 8.6 档案原件（e_pi_archive/，未改动）
- 英文主论文 tex、中文合并版（md/docx）、九轮笔记、研究报告（md/html）、50项审计台账、meiburg_full.md、4脚本+证书、Lean 骨架+执行手册。

## 8.7 VM 侧（C:\Users\Lgnatius\Desktop\RM\）
- vm-setup.sh / vm-fix-tex.sh / vm-setup-report.txt / vm-setup.log（Linux 由 Claude 负责）

---

# 第九部分：综合判断与建议

## 9.1 现实判断
1. 形式化侧接近完整：16 定理无 sorryAx，H′ 机器验证，剩余 F1 纯工程可完成。
2. 数学侧无突破：九轮 + 本机执行，四路线结构性断裂，条件框架全悬于未证猜想。
3. 诚实边界：任何声称"证明 e+π 无理性"的文本按 §7 甄别。

## 9.2 建议执行顺序
**近期（无新数学风险）**：F1 补 T3 → F3 μ(e)=2 → F2 Meiburg。
**长期**：F4 e/π 超越形式化。
**数学探索（高风险）**：现有路线已全部探明障碍，真正突破需 Schanuel(1,iπ) 实例 / μ(π)>2 / 带算术控制的新加法恒等式，均无人做到；不应在已断裂路线重复投入。

## 9.3 一句话决策依据
**"把论文推导完全形式化"（F1–F3）可达、有价值、无新数学风险；"证明 e+π 无理性"是世界未解之谜，本项目无法也不应声称做到。** 两者不可混淆。

---

## 附：关键来源

**档案内部**（已读全）：研究报告.md、第一至九轮笔记、定理与来源审计台账.md（50项）、meiburg_full.md。

**时效性外部事实（2026 检索核验）**：
- μ(π) 最新上界 7.101862832357：Bai 2026, arXiv:2609.11276（改进 Zeilberger–Zudilin arXiv:1912.06345 的 7.103205334137）。
- e+π 仍开放：arXiv:2606.17303（2026）；Math StackExchange 5127192（2026-03）。
- Flint Hills 经典收敛性未判定：Dan 2026, arXiv:2609.12338。
- Schanuel 仍未证明：Wikipedia / arXiv:1010.6216。

**经典参考**：Keith Conrad《Irrationality of π and e》；OEIS Wiki《Pi+e》；Math Overflow 33817；朱尧辰《超越数：代数无关性》（中科大社 2024）。