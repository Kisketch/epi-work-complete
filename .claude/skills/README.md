# Claude Code 项目技能（`.claude/skills/`）

Claude Code 只自动发现 `.claude/skills/<name>/SKILL.md`；`.agents/skills/` 是其它代理（Codex/opencode）的目录，Claude Code 不读取。本目录于 2026-11-23 配置。

| 技能 | 来源 | 用途 |
| :--- | :--- | :--- |
| `lean-audit` | 本项目 `.agents/skills/`（原样复制） | 构建 + `#print axioms` 三层公理审计，「作者自报 / 已核实」口径 |
| `novelty-check` | 同上 | 先行文献与引用核查，负搜索口径 |
| `paper-audit` | 同上 | 论文逐项五分法审计 |
| `proof-reasoning` | 同上 | 证明草稿对抗性审查、反例、可证伪计算 |
| `lean-proof` | [leanprover/skills](https://github.com/leanprover/skills) @ `7d3da02`（2026-02-21），Apache-2.0，见 `LICENSE.leanprover-skills` | Lean 官方：逐步写证明、错误优先级 |
| `lean-mwe` | 同上 | 构造最小复现例（本项目大证书 elaboration/kernel 问题的定位） |
| `mathlib-build` | 同上 | mathlib 构建、缓存、`lake` 用法 |
| `lean-setup` | 同上 | elan / 工具链 / 项目初始化 |
| `mathodology-evidence-search` | [sweetcornna/mathodology](https://github.com/sweetcornna/mathodology) @ `49c639648c61`（MIT），见该技能目录 `LICENSE` | 双通道证据核查 + `scripts/verify_refs.py` DOI/arXiv/Retraction 检查 |
| `verified-research` | [sweetcornna/free-search-mcp](https://github.com/sweetcornna/free-search-mcp) @ `9a59cfc3df5b`（MIT），见该技能目录 `LICENSE` | 配合 `free-search-mcp` 核实官网/一手页面与时效性 |

维护约定：
- `.agents/skills/` 与 `.claude/skills/` 须保持完全同步（含 4 个项目核心技能、4 个 Lean 官方快照技能及 2 个研究核查技能）；修改其一时同步另一处。
- 上游技能为原样快照，不做本地修改；更新时重新从上游复制并更新上表的提交号。
- 未纳入、建议按需在用户级安装的：`cameronfreer/lean4-skills`（MIT，含 hooks 与脚本，属完整插件，不宜作为纯文档技能拷入仓库）。安装命令见 README 末尾或：
  `claude plugin marketplace add cameronfreer/lean4-skills` → `claude plugin install lean4@lean4-skills`（安装前请自行确认插件名与 hooks 行为）。
