# epi_work 总览：已完成项目、下一步规划、当前调研与文件夹解读（2026-11-24）

> **位置**：仓库根 `master_overview_20261124.md`（只增不减新增）。**基线**：`HEAD f345d60`，与 `origin/main` 同步，跟踪文件零修改；另有 42 个未跟踪新文件（本轮产物，见 §5.7）。
> **读法**：§1 一句总判断 → §2 已完成（对照表）→ §3 下一步 → §4 调研 → §5 文件夹逐项解读。enskaper 口径遵循 [`AGENTS.md`](AGENTS.md)：「作者自报，未复跑」「未核到」如实标注；$e+\pi$ 无理性仍是公开问题，本仓库及本轮工作均未改变该基线。

---

## 1. 一句总判断

**工程侧已达可投稿完备度（988 条 Layer A 审计、两次 Colab 独立复现、三轨切片逐字节一致），数学侧的最大增量是临界标度律（334 点零参数数值验证至 m=65536、偏差 ≤1%——数值证据+启发式模型，猜想未证明）；拆分已定为两主稿（A=2C＋临界定理冲 Adv. Math./PLMS，B=2A＋2B 融合 e 作旗舰推论冲 Math. Ann./Selecta）＋ Lean 独立归档；剩余硬仗是 T6 定理化与统一理论，执行受额度路由限制暂停待命。**

---

## 2. 已完成项目

### 2.0 总对照表

| # | 项目 | 类别（AGENTS.md） | 核查状态 | 依据/路径 |
|---|---|---|---|---|
| C1 | 环境配置与 GitHub 同步 | 文献核查/工程 | 已实测（命令输出在案） | §2.1 |
| C2 | 阅读与现状核查（F1/F2 闭合发现） | 文献核查与复现 | 仓库文档已读；Lean 结论按仓库口径，未复跑 | §2.2 |
| C3 | Phase-1：T1 Bowen 清点 | 文献核查与复现 | rg 实测行号；Lean 未复跑 | [bowen_dependency_inventory_20261124.md](verification/bowen_dependency_inventory_20261124.md) |
| C4 | Phase-1：T2 障碍清单（20 步） | 文献核查与复现 | 定义照录；Lean 未复跑 | [generalization_obstacle_list_20261124.md](verification/generalization_obstacle_list_20261124.md) |
| C5 | Phase-1：T3 临界扫描（334 点） | 有限计算 | 脚本+JSONL+日志可复查；判据属 R2 类 | [critical_point_scan_record_20261124.md](verification/critical_point_scan_record_20261124.md)、[addendum](verification/critical_point_scan_addendum_20261124.md) |
| C6 | T6 临界标度猜想 C1–C3 + §8 证明骨架 | 条件结果（猜想）+ 启发式 | 未证明；证据=数值+模型 | [T6_critical_scaling_conjecture_20261124.md](verification/T6_critical_scaling_conjecture_20261124.md) |
| C7 | 拆分方案 v1→v2（两主稿打包） | 规划/分析（非数学结果） | 基于实测结构与已核书目 | [paper2_split_plan_20261124.md](paper2_split_plan_20261124.md) |
| C8 | flash 批次（E1/E6/E7/E9/E10） | 文献核查/起草/有限计算 | 全部落盘并经主会话验收 | [flash_batch_v2_acceptance_20261124.md](verification/flash_batch_v2_acceptance_20261124.md) |
| C9 | 期刊版图 + KMS 素材 | 文献核查与复现 | 证据分级；部分未核到 | [journal_landscape_20261124.md](verification/journal_landscape_20261124.md)、[kms_comparison_materials_20261124.md](verification/kms_comparison_materials_20261124.md) |
| C10 | 文献调研包 v1（8 外搜） | 文献核查与复现 | 摘要级互证/负搜索 | §4.1（全文在记忆 + 本节） |
| C11 | 规划与记忆归档 | 工程 | 4 份规划 + 3 条记忆已落盘 | §5.1、PI 规划归档 |

### 2.1 环境配置与同步（C1）

- 工具链实测：`.venv`（Python 3.12.14 + mpmath 1.3.0 + sympy 1.14.0，数值统一入口；系统 python 3.13.15 无 mpmath）；elan 4.2.4（含 v4.35.0/v4.36.0，项目锁 v4.35.0）；MiKTeX 26.5；git 2.55.0。
- 本地落后 GitHub 5 提交 → 安全快进 `190c02c → f345d60`（26 文件 +2464/−15），与 `origin/main` 完全同步。
- 环境自检计算（类别 4）：e+π 50 位小数、连分数前 25 项、$q\le10^6$ 收敛项 13 个；脚本与输出在 `%TEMP%\epi_envcheck\`（仓库外，可选入档）。**它没做到什么**：纯环境自检，不构成任何数学进展。

### 2.2 阅读与现状核查（C2）——含一个改变规划的发现

- 通读 README、REPOSITORY_STRUCTURE、progress_and_path_analysis（2026-11-13 历史档）、paper2 摘要与多残差定义段。
- **发现**：[FlintHills.lean](epi_formal/EpiFormal/FlintHills.lean) 头注与 `Audit.lean:135` 证实 11-13 文档中的 **F1（T3 缺口）与 F2（Meiburg 公理→定理）均已闭合**——`meiburg_criterion` 现为定理；全库 16 处 "sorry" 字样逐条核对全在注释中；源码 `axiom` 仅剩 3 条经典白名单。形式化侧唯一剩余经典项为 F3（$\mu(e)=2$ 公理→定理）。

### 2.3 Phase-1 三项（C3–C5，按 PI《新努力方向与路径》第一段）

- **T1**：主稿 28 处命中分类 a=16/b=0/c=8/n=4；Lean 133 处全为替代机器命名；论文一 0 依赖；**实质剩余依赖只有 R1（开区间严格性）与 R2（配点脚本谱半径=1 判据）**；附带 `slice_index.csv` 陈旧与摘要/正文口径差两项卫生问题。R1 有去 Bowen 路线（上端点左移重跑整数证书）。
- **T2**：证明拆 20 步，[AP] 承重仅 6 处；**定义层把核 S 与尾剩余类绑成同一 S，推广第一刀是解耦为 (F,R)**；极限公式对 [AP] 多为便利性依赖；给出结构字母表最低条件 (C1)–(C5) 与待证项 T1–T5。
- **T3**：R7 配点法推广到一般 $A_{m,S,B}$；自检 10/10 落入内核核验开括号；$n=16$ vs $24$ 差 ≤1e-15；$s_0$ 表 69 集合，定出临界窗口 $S_j=\{3,4,5,6,j\}$（j=9 超 / j=10 次）；**334 点扫描 + 标度模型零自由参数验证**（m=65536 处偏差 1.003–1.005）：$\varepsilon(\varepsilon+\eta)m^{1+\varepsilon}=d\kappa$，临界指数 $1/2$，交叉尺度 $m^*=d\kappa/\eta^2$，超临界前因子 $d\kappa/(2(2s_0-1))$（README 列为未解决，对 {1,2} 预测 33.43 vs 实测 32.86）。

### 2.4 T6 猜想（C6）

C1（临界指数½+振幅 $\sqrt{d\kappa}/2$）、C2（统一标度律）、C3（交叉尺度）+ §8 极点分解引理 $C_S(p)=\kappa/(p-2s_0)+O(1)$ 六步证明骨架与 Lean 双路径（务实：一条新白名单公理 + 内核隐式代数；彻底：谱隙形式化，mathlib 工具未核到）+ 对 T2 (C3) 的修正建议（尾调和和发散）。**状态：猜想，未证明。**

### 2.5 拆分方案（C7）

- v1：三稿一补（P2A/P2B/P2C/S）+ 六维打分（P2A A− / P2B B+→A+ / P2C A−→A+）+ 五块垫脚石 + 投稿排序。
- v2（吸收 PI 提供的外部深度调研 code_artifact.html）：**改为两主稿**——主稿 A = 2C+T6（25–30 页，冲 Adv. Math./PLMS）；主稿 B = 2A+2B 融合、**e 降为旗舰推论**（30–35 页，冲 Math. Ann./Selecta）；Lean 独立 Zenodo 归档；arXiv 推迟到临界定理后；AI 合规与去工程化叙事要求；对标锚点四件。

### 2.6 flash 批次与验收（C8）

- 任务书 v1（E1/E3/E5）+ v2（E6/E7/E9/E10）全部写明任务/提示词/目标/路径/验收；子代理两次死于托管配额（用户确认耗的是 5.4），但**死前全部落盘**：E1 章节地图 CSV、E6 索引+逐字节核对（主稿 283,403 字节 SHA 一致）、E7 三篇前言 v2（逐定理带行号、项目计数隔离、占位句明示未证，AuditResidueCert 归属留我终稿决断：应计入 P2C）、E9 KMS 素材（6 篇+1 专著+2 补充+4 背景，证据分级）、E10 补丁脚本（我实跑 dry-run：锚点 L157–162、纯插入、git 零修改行，已备待 PI 审阅）。E3 两段扫描由子代理执行完毕（退出码 0），分析与增补由我收口。
- E5 期刊版图：14 刊 30 条代表论文（24 完整/6 有未核到字段）；我抽查 arXiv 页核实 Banaji–Kolossváry 条目无误。
- 验收台账见上表 C8 行。附带问题：`Python/` 误入目录待处置。

### 2.7 文献调研（C9–C10）

见 §4。最重要两条：**CLU 刊载地补齐**（Trans. AMS 373 (2020) no.2 pp.1009–，四源互证）——这是等差数字母表方向的最近先例，统一理论新颖性定位必须引用并区分；**Nakajima–Takahasi Adv. Math. 482 (2025) 110635** 坐实（「一般原理进 Adv. Math.」的活证据）。

### 2.8 记忆与规划归档（C11）

- 规划文件（根）：[development_plan_20261124.md](development_plan_20261124.md)、[integrated_advancement_plan_20261124.md](integrated_advancement_plan_20261124.md)、[paper2_split_plan_20261124.md](paper2_split_plan_20261124.md)（§9 v2 修订）、[PI_新努力方向与路径_20261124.md](PI_新努力方向与路径_20261124.md)（PI 原文逐字归档）。
- 记忆（三条 workspace）：文献调研包 v1、下一阶段研究清单、会话状态摘要（压缩锚点）。

### 2.9 仓库既有成果（仓库口径，指针式）

两篇主论文（论文一 72 页 + 论文二 63 页，零编译错误）、Lean 4 v4.35 工程（344 文件、Audit 937+27+24=988 条、0 sorryAx、3 白名单公理）、两次 Colab 独立复现、32/50/450/2500 位数值体系。权威口径见 [README.md](README.md) 第一节对照表与 §五「它没做到什么」。**唯一硬结论仍是：$e+\pi$ 与 $e\pi$ 至少其一超越。**

---

## 3. 下一步规划

| 优先级 | 事项 | 内容 | 执行者 | 依赖/状态 |
|---|---|---|---|---|
| P0 | T6 定理化 | 极点分解引理纸面证明（缺口 a/b/c 逐个闭：谱隙陈述、Kato 解析性、Bowen 桥接引理）→ Lean 陈述 → Layer A（先走务实路径：一条新白名单公理） | 我 | 引文待核（Hensley/MU/JP）；CLU Thm 2.3 读本地 PDF |
| P0 | E10 与前言审阅 | PI 审阅补丁新增句措辞 + 三篇前言草案 → 批准后执行补丁 → 重编译验证 | PI 审、我执行 | E10 脚本已备 |
| P1 | 两主稿装配 | 主稿 A（C1–C5+T6）、主稿 B（A+B 块+e 旗舰重述）的 frontmatter 定稿与 tex 包装；审计子集声明按篇裁剪；companion 声明 | flash/muse-spark 起草、我审校 | 需额度路由（见 P3） |
| P1 | E9 补齐 | KMS 素材已落盘（E9 实际交付）；剩余：Stratmann 合著期刊版 2–3 条（线索 arXiv 1006.5693） | 同上 | journal_landscape 已有 JKM/GJK 条 |
| P1 | 统一理论 | T2 施工图实施：(C1)–(C5) 定义节、统一定理陈述、KMS 对照节正文、sofic 最小推广；地板条件先定 (C3) 措辞（调和和发散），反例 $A=\{2^{2^k}\}$ 数值先行 | 我（数学）+ 执行层（检索） | T6 与地板条件互为输入 |
| P2 | 论文一攻线 | 轴 B ≤3 个月预注册闸门；条件靶点季检（μ(π)=2 等）；Arb 管线复用；**禁做计算→无理性路线** | 我 | 持续守势 |
| P2 | 工程卫生 | ①`Python/` 处置（PI 定：删或 gitignore）；②slice_index 新旧索引关系说明（一行注释）；③提交前体检三件套；④约 45 个新文件分批 commit（建议按主题分 4–5 个提交：规划/扫描/T6 与猜想/拆分产物/任务书台账） | PI 定 + 我执行 | 只增不减 |
| P2 | 路由解锁 | 用户在 UI 把「执行者」模型切到 muse-spark 连接（d8bae60b）→ 后续执行活改派该 Saved Agent | 用户操作 | 在此之前不派代理 |
| P3 | 发表节奏 | arXiv 推迟到临界定理后；梯度投稿（主稿 A 先行评估 Adv. Math./PLMS；主稿 B 随后）；AI 声明与人工复核说明按刊补齐（政策原文引用前先核） | PI 定 | — |

---

## 4. 当前调研状态

### 4.1 文献包 v1（8 外搜；检索摘要≠打开原文者已标）

| # | 条目 | 状态 | 来源 |
|---|---|---|---|
| ① | CLU：Trans. AMS 373 (2020) no.2 pp.1009– | 已核到（止页未核到） | UConn 作者页 + arXiv 2408.06330v2 参考文献 + AMS 目录 PDF + UNT CV |
| ② | Nakajima–Takahasi：Adv. Math. 482 (2025) 110635 | 已核到 | 作者页 + ScienceDirect 摘要 |
| ③ | DFSU（2007.10554）：2023 年刊出 | 部分（刊名未核到） | UNT CV（截断）+ Urbański 站点 50 页 PDF |
| ④ | JP 2018（E2 百位）：Adv. Math. 325, 87–115 | 部分（外部转述 + AMS 引文佐证） | arXiv:1611.09276 存在；卷页待独立核 |
| ⑤ | Hensley 1992：题名线索 | 部分（刊名卷页未核到） | 一篇引用文献的参考文献表；另有其 DCDS 2012 综述为线索 |
| ⑥ | KMS 相变 2020–2026 | 负搜索 | 与 E5 一致；在范围可核条目仅 JKM 2021、GJK 2022 |
| ⑦ | 无限字母表≥1/2 定理 | 负搜索（支持稀疏反例推断） | 无直接命中 |
| ⑧ | Mauldin 维数函数锚点 | 未核到 | 主稿 B 在核实前不得引用 |

### 4.2 期刊版图（E5，证据分级；我抽查 1 条通过）

14 刊 30 条：Adv. Math. 与 Trans. AMS 各有 Banaji–Kolossváry 2024 / Kesseböhmer–Niemann 2022、Banaji–Fraser 2023 / K–N–Zhu 2023 两条完整条目；Nonlinearity、ETDS、JFG、DCDS、CRAS、PAMS、Stoch. Dyn. 各有强专业刊条目；S 轨（Lean）条目多为 A 级（未逐页打开）。6 条有未核到字段；Inventiones/JEMS 等本次负搜索。详见 [journal_landscape_20261124.md](verification/journal_landscape_20261124.md) 与证据台账。

### 4.3 KMS 素材（E9，已落盘并核验形式）

6 篇主条目（K–S 2012 DCDS-A、KMS 2012 ETDS 32:989–1017、Bonanno 2023 Mathematics、Dodds arXiv 1994 论文、Jordan–Rams 2011、Rapaport 2018 IJM）+ KMS 专著 2016 + Iommi–Yayama 2017 + Tang 预印本 + BG1–BG4 背景（K–S 2007 Crelle、Prellberg–Slawny 1992、Prellberg 2003、Yuri 三文）；「capped-height」精确短语负搜索。详见 [kms_comparison_materials_20261124.md](verification/kms_comparison_materials_20261124.md)。

### 4.4 对标锚点（外部报告给出；核对状态各异）

JP 2018（部分）、DFSU 2020（部分）、Nakajima–Takahasi 2025（已核）、Wang–Wu/KW（未核）。使用规则：已核者可引用；其余引用前必须经出版社/zbMATH 独立核实。

### 4.5 合规与未核到清单

Annals/Elsevier 2026 AI 政策原文未核到；Hensley 1992 未核到；DFSU 刊名未核到；CLU 止页未核到；Mauldin 锚点未核到；mathlib PF/谱半径工具未核到。

### 4.6 开放研究问题（调研未解决，需做数学）

地板条件的确切形式（调和和发散猜想）；$s_0=1/2$ 恰成立的整数集合存在性；$\kappa(S)$ 随 $S$ 的连续性；sofic 核的无 Bowen 维数公式。

---

## 5. 文件夹解读（逐项，截至本文件落盘时）

**根目录文件**：

| 文件 | 角色 | 状态/注释 |
|---|---|---|
| [AGENTS.md](AGENTS.md) | 项目宪章（诚实分类、引用/形式化/计算纪律） | 跟踪；一切工作的纪律源 |
| [README.md](README.md) | 仓库权威中文总览（成果对照表、公理清单、复现指南、边界） | 跟踪；对外第一入口 |
| [REPOSITORY_STRUCTURE.md](REPOSITORY_STRUCTURE.md) | 六层结构导航（L1–L6）与版本守恒谱系 | 跟踪 |
| [progress_and_path_analysis.md](progress_and_path_analysis.md) | 2026-11-13 历史研究状态评估（九轮+本机） | 跟踪；**F1/F2 建议已过时**（均已闭合），读作档案 |
| [development_plan_20261124.md](development_plan_20261124.md) | 本轮早期独立规划（形式化收尾+延展五项） | 新增；部分被合并计划取代排序 |
| [integrated_advancement_plan_20261124.md](integrated_advancement_plan_20261124.md) | PI 规划与早期规划的合并执行计划 | 新增 |
| [PI_新努力方向与路径_20261124.md](PI_新努力方向与路径_20261124.md) | PI 规划逐字归档 | 新增；原稿在 PI 桌面 |
| [paper2_split_plan_20261124.md](paper2_split_plan_20261124.md) | 拆分方案 v1+v2（两主稿打包） | 新增；§9 为 v2 修订 |
| 本文件 | 总览（已完成+规划+调研+文件夹解读） | 新增 |
| `paper2_numeric_check_20261124.py` / `_output.txt` | PI 侧常量交叉核对脚本与输出（只读） | 未跟踪非我产物；是否入库由 PI 定 |
| `rename_english_20261121.ps1`、`reorganize_step1/2_20261121.ps1` | 历史重组脚本（可追溯） | 跟踪；勿重跑 |
| `opencode.json` / `.bak-*`、`.gitignore` | 本地运行时配置与忽略规则 | 跟踪/忽略见文件 |
| `Python/` | **误入目录**：uv Python 3.15 安装 | 未跟踪；处置待 PI 定（删/忽略） |

**[paper1_e_plus_pi/](paper1_e_plus_pi/)**：`01_main_paper/`（72 页主稿 tex/pdf/log，9 文件）、`02_companion_paper/`（历史 B 稿，3 文件）、`03_submission_prep/`（投稿材料，19 文件）、`04_formalization_audits/`（早期审计，9 文件）、`05_research_process/`（分轮研究，211 文件）、`06_historical_versions/`（演化备份，81 文件）；索引 `00_PROJECT_INDEX.md`、`00_merge_review.md`、`00_research_status.md`。本轮未动（除阅读）。

**[paper2_spectral_gap_dimension/](paper2_spectral_gap_dimension/)**：主稿 tex（276.8KB）/pdf/log + tectonic 日志 + README；补丁脚本家族（`patch_*_2026112*.py`，追加式修改是本仓库允许的改法）；**新增** `patch_abstract_scope_20261124.py`（E10，dry-run 已验，未执行修改）。子目录：`split/`（见下）、`historical_versions/`（冻结旧稿）。
`split/` 内：`src_sections/`（28 个 .tex：11 基础切片 + shared + 变体；E6 已证 11 切片拼接逐字节=主稿）+ 四轨草案目录（各含 MANIFEST + ~1KB draft 包装）+ `README.md`、`BUILD_TRIAL_LOG.md`、`intro_trim_2*.py`、`undef_ref_audit.py`；**新增** `slice_index_20261124.csv`、`slice_concat_check_20261124.md`、`frontmatter-2{A,B,C}-v2.tex`、`frontmatter_v2_report_20261124.md`。

**[epi_formal/](epi_formal/)**：Lean 4 v4.35 工程：`lean-toolchain`（锁 v4.35.0）、`lakefile.toml`、`lake-manifest.json`；`EpiFormal.lean` 总入口 + `EpiFormal/` 337 模块；三审计入口（`Audit.lean` 937 条、`AuditResidueCert.lean` 27 条、`AuditResidueMultiAsymptotic.lean` 24 条）；`EpiFormal2{A,B,C}_Draft.lean` 三轨草案 + `SPLIT_DRAFT_LOG.md`、`check_draft_imports.py`；治理文档 README/LEMMA_AUDIT/PROOF_GAPS/FINAL_REVIEW（2026-11-14 历史口径，读作档案）。本轮只读未构建（PI 指示）。

**[verification/](verification/)**：分两类。(a) 本轮新增：扫描四件套（`critical_point_scan_20261124.py` 含自检/s0/xcheck/scan 四阶段、`_config*.json` ×3、`_analyze`、`_diagnostics{,_v2}.md`、`_record`、`_addendum`、`critical_scaling_check_20261124.py` 与输出 ×2、`critical_point_scan_20261124.jsonl/.log/.stdout.txt` 数据）、[T6 猜想](verification/T6_critical_scaling_conjecture_20261124.md)、[Bowen 清单](verification/bowen_dependency_inventory_20261124.md)、[障碍清单](verification/generalization_obstacle_list_20261124.md)、[章节地图 CSV](verification/paper2_section_map_20261124.csv)（注意它比我的 21 节多出 `\section*` 的 AI 声明节与首尾，共 24 行）、[期刊版图](verification/journal_landscape_20261124.md)+证据台账、[KMS 素材](verification/kms_comparison_materials_20261124.md)、[任务书 v1/v2/v3](verification/flash_task_briefs_v3_20261124.md)、[批次验收](verification/flash_batch_v2_acceptance_20261124.md)、E7 检查脚本、E10 预览。(b) 仓库既有：`verify_*.py` 证书脚本族、`audit_*.log`、`check_audit_reconcile.py`、Colab 复现记录、CMMS 核查、`reference_pdfs/`（含 CLU_1805_11904.pdf——T6 下一步要读 §2）、台账三件套（总索引/成果清单/复现指南）。既有部分未逐项重读，以 `verification/README.md` 与台账为准。

**[papers/](papers/)**：仅 `README.md`（arXiv 落盘说明）。**[scripts/](scripts/)**：`probe_paper_search.js` 探针及输出。**[downloads/](downloads/)**：`1211.2494.pdf`、`1805.11904v1.pdf`（文献缓存）。
**被忽略目录**：`.venv/`（数值环境）、`epi_formal/.lake/`（~8.49GB Mathlib 缓存，勿删）、`.zwork/`（运行时保留，不可写）、`.agents/`/`.claude/`/`.opencode/`（Agent 运行时）。

---

## 6. 诚实边界

1. 本文件是**规划与核查记录**，不含任何新数学定理；凡涉数学结论处均回指其来源文件与状态标注（已证/猜想/数值/未核到）。
2. 所有「已核实」为仓库口径（作者自报 + 两次 Colab 独立复现）；主会话与子代理均未复跑 Lean（PI 指示）。
3. 书目字段凡未打开原文者一律「未核到」，不补全；负搜索≠不存在。
4. $e+\pi$ 无理性仍是公开问题；唯一硬结论仍是 $e+\pi$ 与 $e\pi$ 至少其一超越。

---

## 7. 2026-11-24 晚间增补（T6 状态升级与本轮新文件）

**T6 状态变化（重要）**：旧文件 [T6_critical_scaling_conjecture_20261124.md](verification/T6_critical_scaling_conjecture_20261124.md) 仍为猜想草案，**其状态已被本轮新节部分超越**，读作历史档案：

| 对象 | 旧状态 | 新状态 | 依据 |
|---|---|---|---|
| 极点分解 $C_S(p)=\kappa(S)/(p-2s_0)+O(1)$ | 六步骨架，缺口 a/b/c | **[THEOREM] 已证**（显式空间 $A(\{|z-1|<1\})$，Kato + PF） | `split/src_sections/sec-critical-scaling.tex` Lemma `lem:pole` |
| 联合标度极限 $\Phi(x)=(-x+\sqrt{x^2+4d\kappa})/2$ | 猜想 C2（固定 $\eta$ 形式） | **[CONDITIONAL]** 条件于 Hypothesis `hyp:tail`（临界窗尾方程一致性） | 同上 Theorem `thm:critical-scaling` |
| 临界指数 $1/2$ 与振幅 $\sqrt{d\kappa}/2$ | 猜想 C1 | **[CONDITIONAL]** 由上式 $x=0$ 推出 | 同上 Corollary `cor:critical-exp` |
| 超临界常数 $d\kappa/(2(2s_0-1))$ | 猜想推论 | **[HEURISTIC]** 未证；数值差 2% | 同上 Proposition + Remark `rem:supercritical-status` |
| 固定 $\eta$ 的 C2 | 陈述为对任意有限 $S,B$ | **[PROVED] 为假**（次临界比 $1.19=C_S(1)/(\kappa/\eta)$） | 同上 Remark `rem:naive-C2-false` |
| 主稿 L3940 尾方程 | $m^{-\varepsilon}$ | **[PROVED] 应为 $m^{-1-\varepsilon}$**（排版错误，特例 $F_{m,m}$ 判定） | 同上 Remark `rem:typo` |

**本轮新增文件**（只增不减，未改任何既有文件）：
- [`split/src_sections/sec-critical-scaling.tex`](paper2_spectral_gap_dimension/split/src_sections/sec-critical-scaling.tex)——T6 证明节（18,249 字节，未编译；`\cite` 需与增补文献合并）。
- [`split/src_sections/refs-addendum-20261124.tex`](paper2_spectral_gap_dimension/split/src_sections/refs-addendum-20261124.tex)——6 条新文献（Mayer 1991、JP 2018、Kato 1976、Hensley 1992、Parry–Pollicott 1990、Mauldin–Urbański 2003），**不得直接改 `refs.tex`**（会破坏 11 切片字节一致性），装配时合并。
- [`verification/deep_research_and_polish_20261124.md`](verification/deep_research_and_polish_20261124.md)——调研结论、逐篇打磨清单、论文一进展与诚实边界。
- [`verification/verify_c2_discrepancy_20261124.py`](verification/verify_c2_discrepancy_20261124.py)（+ `_output.txt`）——复算 C2 固定 η 形式的 1.19 差异与标度函数代数残差（类别 4）。

**未完成（下一步）**：① 新节编译与 `\cite` 合并；② 证 Hypothesis `hyp:tail` 的临界窗一致性（把 (iv) 的预解式估计从 $\varepsilon=O(1/m)$ 推到 $O(m^{-1/2+\delta})$）；③ 超临界常数（需不依赖 Hurwitz 尾近似的预解式分析）；④ Lean：先以一条新白名单公理 `C_S_pole_decomposition` 引入，再在内核内做标度极限的实代数部分。
**构建结果（2026-11-24 第 1 轮续跑，MiKTeX 26.5 pdflatex 两遍）**：

| 产物 | 页数 | exit | 未定义引用 | 备注 |
|---|---:|---:|---:|---|
| `paper2_spectral_gap_dimension_v3_20261124.tex/.pdf` | **69** | 0 | 0 | 主稿+T6 新节+尾方程修正+6 条新文献；原稿 63 页 |
| `split/2C…/paper2A_critical_scaling_draft_20261124.tex/.pdf` | **30** | 0 | 0 | 主稿 A（2C+T6），25–30 页目标内 |
| `split/2B…/paper2B_unified_draft_20261124.tex/.pdf` | **36** | 0 | 0 | 主稿 B（2A+2B 融合），略超 35 页 |
| 既有 2A/2B/2C draft（回归） | 24 / 15 / 25 | 0 | — | 未改动 |

摘要词数：2C v3 = 200（v2 = 192，加 T6 后压回 200）；2B v3 = 128（合并、$e$ 降旗舰推论）。构建中发现并修掉：中文进 bibliography 的致命错误、`\C`/`\Log`/`hypothesis` 未定义、尾方程排版错、摘要超长。详见 [`BUILD_LOG_20261124.md`](paper2_spectral_gap_dimension/BUILD_LOG_20261124.md)。

**本轮再新增**：`patch_t6_integration_20261124.py`（append-only，默认 dry-run，`--apply` 只写新文件并校验原稿 SHA 不变）、`refs-2C-v3-20261124.tex`（21 条 bibitem）、`frontmatter-2C-v3-20261124.tex`、`frontmatter-2B-v3-20261124.tex`、两份装配草案及 PDF。

**2026-11-25 第 2 轮（E17–E19 执行完毕）**：Hypothesis `hyp:tail` 已删除并升级为 `lem:resolvent-uniform` + `lem:master`（均匀预解展开 + 主方程，下界侧 `K=⌈e^{m³}⌉` 非循环），`thm:critical-scaling`/`cor:critical-exp` 升为定理（modulo 仓库判定准则）；主稿 B 压至 35 页（`sec-num-2A` 换替换段 + `\label{sec:num}` 补齐）；全线重编译：v3 70 页 / 主稿 A 31 页 / 主稿 B 35 页 / 三轨 24/15/25，均 0 未定义引用。补丁 `patch_e17_upgrade_20261125.py`；README 追加 §六；lake build 重跑中（首次后台跑错目录，已在 `epi_formal/` 重启）。
