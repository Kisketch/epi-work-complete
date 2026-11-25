# flash 执行任务书 v2（2026-11-24）——论文二拆分执行批次

> **分工**（PI 2026-11-24 指令）：机械性任务派给 GLM-5.3-Flash（经 workflow 引擎派发的临时代理）；关键、困难任务由主会话（GLM-5.4）直接操刀。本文件是派给 flash 的任务书原文：每条含**任务、提示词全文、目标、路径、验收**。主会话在收货后逐项检查成果（读文件、抽查正确性），不合格打回。
> **全局硬规则（每条适用）**：只增不减——只允许新建文件，禁止修改/删除任何既有文件；禁止 git 写操作；禁止 lake；禁止 pdflatex；禁止联网（仅 E9 可用 web）。先读 `AGENTS.md`。回答 ≤1000 字并给出产出文件的 workspace 相对路径。
> **工作区**：`<repo-root>`（PowerShell 5.1）。

---

## E6｜真实切片索引与逐字节核对

- **任务**：为 `paper2_spectral_gap_dimension/split/src_sections/` 的全部 28 个 .tex 建立真实索引，并对 11 个基础切片（sec-preface, sec-class, sec-spectrum, sec-finite, sec-weights, sec-gauge, sec-growing, sec-windows, sec-resasymp, sec-num, sec-verification）做「拼接 vs 主稿」的 SHA-256 逐字节核对。
- **提示词**：你只做抽取与核对。步骤：①列出 src_sections 全部 .tex（名称、字节数）；②对每个基础切片：读首行与末行非空行，在主稿 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（4463 行）中用精确字符串匹配定位起止行；③核对相邻切片连续（止行+1=下一起行）、总计覆盖 4463 行；④用 PowerShell 把 11 个切片按顺序字节拼接，`SHA256` 与主稿哈希比对；⑤写出两个新文件（见路径）。所有行号/哈希来自实际命令输出；不一致时报告首个差异行号。
- **目标**：一份机器可复查的切片索引 + 逐字节一致性结论。
- **路径（产出，均为新文件）**：`split/slice_index_20261124.csv`（列：file,bytes,main_start,main_end,contig,note；基础切片 11 行 + 其余节文件 17 行 note=variant/shared）；`split/slice_concat_check_20261124.md`（哈希两个值 + 一致/不一致结论 + 首差异行）。
- **验收**：CSV ≥28 行；连续性结论明确；两个 SHA-256 原文出现；无既有文件被修改（`git status --porcelain=v1` 只有 `??`）。

## E7｜三篇 frontmatter 起草（v2，新文件）

- **任务**：为拆分后的三篇（P2A 谱离散化与精确规范 / P2B 一般递推与结构字母表理论 / P2C 窗口、残差与临界相变）各起草一份**英文 frontmatter**（标题 + 摘要 ≤200 词 + 诚实声明段），写成新文件，不碰既有 `frontmatter-2X.tex`。
- **提示词**：你是论文 frontmatter 起草员。素材来源（只读）：主稿摘要 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex` L107–166（照录其诚实口径与句式）；主稿章节地图（摘要行号：P2A ← L417–1843 各节；P2B ← L1844–2881；P2C ← L2884–4052）。要求：①每篇标题以 *On the …* 风格、≤16 词；②摘要只陈述**本篇**的定理内容与 Lean 验证状态（照录主稿中本篇区块对应的内核声明句式，例如 P2A 引 L154–163 的验证句式但只列本篇模块）；③每篇必须含两句：本篇覆盖的审计子集声明（模块名照抄主稿中该区块引用的 .lean 名）+ "does not resolve the open problem of the irrationality of $e+\pi$"；④P2B 摘要在统一理论位置写占位句 `[Unified structural-alphabet theorem: to be inserted]`；P2C 摘要在临界情形位置写占位句 `[Critical scaling theorem: to be inserted]`；⑤每篇末尾加 companion 句：*The full 63-page version containing all proofs is available as a companion manuscript.* 不得改动任何既有文件；三个新文件 + 一份对照报告。
- **目标**：三篇可独立投稿的 frontmatter 草案，供主会话审校后经补丁脚本入轨。
- **路径（产出）**：`split/frontmatter-2A-v2.tex`、`split/frontmatter-2B-v2.tex`、`split/frontmatter-2C-v2.tex`、`split/frontmatter_v2_report_20261124.md`（报告：每篇声称的定理清单 + 对应主稿行号 + 占位句位置）。
- **验收**：三个 .tex 可读、无 LaTeX 语法裸错（配对花括号检查）；报告逐条给出主稿行号；两处占位句按原文标注；无既有文件被修改。

## E9｜KMS 相变对照资料（需联网）

- **任务**：为 P2B 的「与 Kesseböhmer–Munday–Stratmann 热力学形式体系相变对照专节」收集资料：找 4–6 篇 2010–2026 年的相关论文（Farey/Gauss 系统的相变、weak Gibbs、capped-height、Kesseböhmer–Stratmann 维数谱），逐篇给出：题名、作者、年份、刊载（卷页/DOI，**只能来自实际打开的页面**，打不开写「未核到」）、其相变/临界结论的 1–2 句英文原文摘录（照录）+ URL。
- **提示词**：你是文献检索员。只检索与抄录，不评价本论文；每条证据标注等级（P·DOI / P·卷页 / R 二手 / 未核到）；负搜索≠不存在，末尾写明检索词族与覆盖范围；无 web 工具则回答「无 web 工具，未执行」。
- **目标**：P2B 对照专节的原始素材页（供主会话写成专节）。
- **路径（产出）**：`verification/kms_comparison_materials_20261124.md`。
- **验收**：≥4 篇且每篇有 URL 与英文摘录或「未核到」标注；与本论文无任何评价性文字。

## E10｜摘要口径补丁脚本（只起草，禁止执行修改）

- **任务**：起草一个幂等补丁脚本，用于把主稿摘要的「内核之外内容」自报从 2 处补全为 §verification 所列 4 处（PF 特征向量、开区间严格性、临界边界渐近率与超临界首项常数、e+π 开放问题声明）。**只写脚本与预览，不执行修改。**
- **提示词**：你是补丁脚本作者。脚本要求：①文件 `paper2_spectral_gap_dimension/patch_abstract_scope_20261124.py`；②默认 dry-run：只打印将插入的文本与锚点行号，不写文件；③仅当命令行给 `--apply` 且用户输入 `yes` 才落盘，且落盘方式为**在锚点句后插入一个新增句**（不得删除或改写任何既有字符——只增不减）；④锚点：主稿 L157–160 的句子 `Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence input ... remain outside the Lean kernel`（rg 实测行号）；⑤新增句内容（英文，照录 §verification 的四项口径，来自 L4393–4401）；⑥附带预览文件写明：锚点原文、新增句、dry-run 输出样例。你不得运行 `--apply`；不得改动任何既有文件。
- **目标**：PI 审阅后一键执行的合宪补丁。
- **路径（产出）**：`paper2_spectral_gap_dimension/patch_abstract_scope_20261124.py`、`verification/patch_abstract_scope_preview_20261124.md`。
- **验收**：脚本 dry-run 可运行且输出预览；`git status` 无 ` M` 行；新增句为纯插入。

---

## 主会话保留（关键/困难，不由 flash 做）

- T6 极点分解引理 $\ C_S(p)=\kappa/(p-2s_0)+O(1)\ $ 的纸面证明骨架与 Lean 化路径（T6 §8，主会话撰写中）。
- 三篇 frontmatter 的审校与合宪性检查（E7 产出后由主会话逐句核对口径）。
- E6 哈希结论的复核、E10 补丁的审查与（PI 批准后）执行。
- 评级、投稿排序、与 PI 规划的对齐（已完成于 `paper2_split_plan_20261124.md`）。
