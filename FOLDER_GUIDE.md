# 文件夹快速导览（FOLDER_GUIDE）

> 两分钟读懂这个仓库。详细的历史与数字见 [README.md](README.md) 和 [REPOSITORY_STRUCTURE.md](REPOSITORY_STRUCTURE.md)；研究纪律见 [AGENTS.md](AGENTS.md)。

## 一句话

这里是 $e+\pi$ 无理性问题相关研究的完整归档，包括两篇主论文及其衍生稿、Lean 4 形式化工程、数值与文献核验包，以及 P1 围攻战役的全过程记录。**诚实基线：$e+\pi$ 的无理性仍是公开问题，本仓库没有证明它，也没有证明 P1（等价于 1、e、π 在 ℚ 上线性无关）。**

## 目录地图

```
epi_work/
├── paper1_e_plus_pi/            论文一（75 页主稿）及其提交准备、形式化审计、研究过程
├── paper2_spectral_gap_dimension/ 论文二（66 页主稿）+ 衍生论文 2D/2E + 无损切片工程 split/
├── epi_formal/                  Lean 4（v4.35.0 + Mathlib）形式化工程，CI 全量构建与公理审计
├── verification/                数值/符号/区间证书、审计日志、对账脚本、参考文献 PDF
├── research/                    新课题笔记（Kahane Q6 等）与 2026-11-24 规划文档
├── logs/                        P1 围攻战役过程记录（账本、交接、评审、证据）——仅供复查，不得引用
├── artifacts/                   围攻战役定理单元 THM-0001..0006（陈述、证明、评审、Lean 副本）
├── registry/                    定理与尝试的总注册表 results.csv
├── papers/  downloads/          文献落盘说明与下载缓存
├── scripts/                     辅助脚本（文献检索探针）
├── .github/workflows/           CI：Lean 构建+公理门禁、Python 核验
└── .agents/  .claude/  .licenses/  研究纪律规则、技能镜像、第三方许可证
```

## 我想……

| 想做的事 | 去哪里 |
|---|---|
| 读论文一 | [paper1_e_plus_pi/01_main_paper/](paper1_e_plus_pi/01_main_paper/README.md)（`paper1_e_plus_pi.tex` / `.pdf`） |
| 读论文二及衍生稿 | [paper2_spectral_gap_dimension/README.md](paper2_spectral_gap_dimension/README.md) |
| 看 P1 围攻战役的结论 | [logs/CAMPAIGN_SUMMARY.md](logs/CAMPAIGN_SUMMARY.md) |
| 看某个定理的陈述与证明 | [artifacts/README.md](artifacts/README.md) |
| 查一个结果的状态与类别 | [registry/results.csv](registry/results.csv)（说明见 [registry/README.md](registry/README.md)） |
| 复核 Lean 证明 | [epi_formal/README.md](epi_formal/README.md)；模块索引见 [epi_formal/EpiFormal/README.md](epi_formal/EpiFormal/README.md) |
| 复跑数值证书 | [verification/README.md](verification/README.md) |
| 了解 CI 检查什么 | [.github/workflows/README.md](.github/workflows/README.md) |
| 了解研究纪律与门禁 | [AGENTS.md](AGENTS.md)、[.agents/rules/next-step-workflow.md](.agents/rules/next-step-workflow.md) |

## 三条约定

1. **正式与非正式分开。**`paper1_*/01_main_paper`、`paper2_*` 主稿和 `epi_formal/EpiFormal` 是正式内容。`logs/`、`artifacts/`、各 `research_process` 目录是过程记录，文件头标有 LOG-ONLY / NON-CANONICAL / DO NOT CITE。
2. **结果一律标类别。**无条件新结果、条件结果、等价改写、有限计算、文献核查（AGENTS.md §2），不夸大。
3. **只增不减。**历史版本与失败尝试都保留，不删除；`verification/verify_repo_integrity.py` 会检查这一点。

## 关于 PDF

- 围攻战役中由用户提供的 Kraaikamp–Liardet 1991、Larcher 1988、Philipp 1967 全文**没有入库**（有版权），仓库里只存已核对的书目与转述。
- 仓库里已有的 PDF 是此前会话加入的，位于 [verification/reference_pdfs/](verification/reference_pdfs/README.md) 和 [downloads/](downloads/README.md)，各目录 README 列明来源。其中一份是期刊正式版，建议人工确认其分发许可。
