# 独立机器全量重建与公理审计（Google Colab，2026-11-23）

**一句总判断**：在一台与作者本机无关的机器（Google Colab Pro High-RAM，8 vCPU / 50 GB，Linux）上，从 GitHub 公开仓库提交 `3563f85` 全新克隆，按 `lake-manifest.json` 锁定的 Lean 4.35.0 + Mathlib v4.35.0（commit `56a005855ea17e0b0958f73ec801ae140b0a1679`）全量 `lake build` 退出码 0，`Audit.lean` 的 937 条 `#print axioms` 输出与仓库中的 `verification/audit_final_20261122.log` **逐条一致（0 条差异）**，`check_audit_reconcile.py` 全部断言通过；`AuditResidueCert.lean` 27 条仅依赖 Lean 基础三公理。据此，按 `AGENTS.md` §5，两篇论文中可追溯到 `Audit.lean` / `AuditResidueCert.lean` 的 Lean 声明由"作者自报，未复跑"改为**已核实**。**它没做到的是**：形式化只证明被形式化的命题；23 条声明使用经典白名单公理（`e_transcendental`、`pi_transcendental`、`mu_e_eq_two`，均为已发表的经典结果但在本项目中以公理引入）；`e+\pi` 的无理性仍是公开问题，本次复现与之无关。

| 项目 | 结果 |
| :--- | :--- |
| 源 | `git clone --depth 1 https://github.com/Kisketch/epi-work-complete.git`，HEAD `3563f85`（其后提交 `0c052c7`、`15fd9d6`、`1a9e760` 未改动 `epi_formal/`） |
| 工具链 | elan 安装 `leanprover/lean4:v4.35.0`；`lake exe cache get` 取 Mathlib 预编译缓存（9031 文件） |
| `lake build`（默认目标 `EpiFormal`，含 `ResidueCertGen/` 200 个证书模块） | `BUILD_EXIT 0`，real 21m14.6s（8 核） |
| `lake env lean Audit.lean` | `AUDIT_EXIT 0`，real 10.1s；937 条，与 `audit_final_20261122.log` 逐条比较差异 0；输出 SHA256 `5f5605a7888ea6ee28ad7f5daab038d83f3a3f0283a60241089aac89a03ff088` |
| `check_audit_reconcile.py` | `ALL RECONCILIATION CHECKS PASSED!`：Core-only 914，whitelisted-classical 23，源码 `axiom` 声明恰 3 条（上述白名单），sorryAx 0，逃逸关键字 0 |
| `lake env lean AuditResidueCert.lean` | `AUDIT_RC_EXIT 0`；27 条，公理集合唯一：`[propext, Classical.choice, Quot.sound]` |

三层公理清单（`AGENTS.md` §5）：
- **Lean 基础公理**：`propext`、`Classical.choice`、`Quot.sound`（914 + 27 条声明只用这一层）。
- **经典白名单公理**：`e_transcendental`、`pi_transcendental`、`mu_e_eq_two`（23 条声明，全部属论文一模块）。
- **项目自加公理**：0。

操作说明：Colab 笔记本由 Claude 经内置浏览器操作；构建日志写在 Colab 本地 `/content/epi_build/` 并在挂载后同步到用户云盘 `MyDrive/epi_build/`；本文件中的数字由笔记本单元格输出逐字转录。本机（3.9–6.9 GB 内存）并行的单线程备份构建在 Colab 结果出来后停止，不作为依据。
