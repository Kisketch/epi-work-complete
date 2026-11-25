# 后续阶段工作流与自动化质量门禁（Next-Step Workflow Rules）

本规则补充 [AGENTS.md](../../AGENTS.md)，用于规范 2026-11-25 之后的所有文献检索、定理修改、Lean 审计、数值校验、多轨编译与投稿准备。

## 1. 文献检索与双通道证据门禁
- **强制双通道**：涉及前沿结论、优先权（Prior Art）或定量对比时，须同时调用本地 `search` MCP（`free-search-mcp`：`search` / `fetch` / `read_doc` / `paper_graph`）与学术一手库（`literature-search-openalex`、`literature-search-arxiv`、Crossref REST、DataCite API、Zenodo/GitHub 原页）。禁止只凭搜索引擎摘要或单一二手转述写入论文。
- **先读后写与多源防伪**：引用正文命题号、作者姓名或数值界前，必须直接打开一手 PDF/源码/官网核对（例如区分 `Chen Tian` 与误转写的 `Chaogui Tian`，区分 `openai/math` 中含 `sorry` 的挑战题面 `ComparatorChallenges/PiExponent.lean` 与主证明文件 `OAI/NumberTheory/PiExponent/Main.lean`）。
- **四重勘误/撤稿核查（Load-Bearing 文献必查）**：
  1. Crossref `update-to` / `updated-by` / `relation`（对 Zenodo/预印本 DOI 须同步查 DataCite，不可只查 Crossref）。
  2. OpenAlex `is_retracted` 与引用勘误反链（注意 OpenAlex 可能漏报 arXiv 撤稿，例如 `2502.03474v2`）。
  3. arXiv `/abs/` 页面版本历史与作者 comment 字段（唯一可直接捕获 `WITHDRAWN` 注释的渠道）。
  4. 针对经典论文（如 1990s *J. Number Theory* 等 Crossref 关系字段缺失文献）追加一次“标题 + Erratum / Corrigendum”专项 Web 检索。
- **自动化参考文献脚本校验**：每次增删改 `.tex` 或研究报告 `.md` 中的文献引用，须执行：
  `py .agents\skills\mathodology-evidence-search\scripts\verify_refs.py <目标文件>`
  **LaTeX 书写约定**：在 `.tex` 文件的 `\bibitem` 中写 DOI 时，禁止使用 `\allowbreak` 切分 DOI 字符串（如 `10.1016/\allowbreak ...`），以免破坏 `verify_refs.py` 与 PDF 超链接提取；长行交由 `{\sloppy ...}` 与 `\emergencystretch` 处理。

## 2. 安全配置与 MCP / 技能镜像规范
- **MCP 配置红线**：仅在用户级 `~/.gemini/config/mcp_config.json` 中维护 `uvx` 固定版本启动项（`free-search-mcp==0.18.2` 与 `papergraph-mcp==1.2.3`）；**禁止运行 `search-mcp-login antigravity`**，禁止手工编辑内部 `config.json`，禁止擅自静默安装 Marketplace 插件。
- **双根技能镜像**：仓库内 `.agents/skills/` 与 `.claude/skills/` 须保持内容一致（含自研 4 项、`leanprover/skills` 4 项快照及 `mathodology-evidence-search` / `verified-research` 与上游 `LICENSE`）。任何一侧更新须同步另一侧并更新 [.claude/skills/README.md](../../.claude/skills/README.md)。

## 3. Paper 1 & Paper 2 编辑与分轨守恒纪律
- **Paper 2 单一真源（SSOT）**：严禁只手工改 `paper2_spectral_gap_dimension.tex` 或某一切片。任何涉及 Paper 2 正文、数值注记或文献表的改动，须用确定性脚本同步修改 `split/src_sections/` 中对应切片（及 `intro-2A.tex` / `intro-2B.tex` / `intro-2C.tex` / `refs.tex`），再按 `slice_index.csv` 的 11 个标准切片重新拼接生成 `paper2_spectral_gap_dimension.tex`。
- **三道工程验收门禁（每次改 `.tex` 后必跑）**：
  1. `py verification\verify_repo_integrity.py` 通过（0 退出码、字节拼接一致、所有 `\bibitem` 100% 被引用、文件数单调不减）。
  2. Paper 1、Paper 2 主稿及分轨 `2A`、`2B`、`2C`、`S` 均经两遍 `pdflatex` 编译通过且 `split/undef_ref_audit.py` 输出 `undef-cites: 0`（跨轨预期 `\ref` 除外；独立投稿前须全量消解或改写为外部引用）。
  3. 严禁修改、删除或自动填充受保护资产；严禁无故删改已有注释与文档字符串。

## 4. 形式化 Lean 4 与高精度数值纪律
- **Lean 核查口径**：本地 `epi_formal/.lake` 可用时，涉及 `.lean` 修改须在 `epi_formal` 下运行 `lake build` 与 `Audit*.lean` 核对 `#print axioms` 三层依赖（`propext`, `Classical.choice`, `Quot.sound` vs 白名单公理 vs 零新增公理）。未在本机复跑的第三方仓库一律维持「作者/第三方自报，未在本机复跑」。
- **严格数值 vs 非严格佐证**：有限分母排除等确定性界须通过 `python-flint` Arb 区间与 exact rational 验证（`verification/rational_exclusion_bound_20261124.py --selftest`），并严守 `AGENTS.md` §2 第 4 类标签；Chebyshev 配点或四阶启发式拟合等数值结果必须在正文和图注中明确标注「non-rigorous numerical corroboration / not proved」。

## 5. 投稿前人工放行门禁（严禁 AI 代签）
Paper 2 尚余 3 项面向投稿人责任的 `% TODO before submission` 占位符，**AI 禁止擅自填写或删除**，须由人类作者在最终投稿前逐项完成并替换：
1. 作者姓名与单位占位符（`[Author name]` — 同步涉及 `paper2_spectral_gap_dimension.tex` 第 32 行与 `2A/2B/2C/S` draft 及 `verify_paper2_merge.py` 锚点规则）。
2. 正文 `Use of AI and formal verification` 节投稿前期刊政策合规声明。
3. `sec:verification` 末尾人工逐行核对论文手稿证明的方法与审阅人声明。
