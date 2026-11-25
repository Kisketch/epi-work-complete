# Lean 草案与分篇接口隔离区（不进 `epi_formal/` 构建、不进主审计）

> 本目录文件**不在** `epi_formal/` 内，故 `lake build` 与
> `verification/check_audit_reconcile.py`（全库 escape 关键字与 3 条源码 `axiom` 严格审计）均不受影响。

## 一、论文分篇 Lean 接口草案（[`paper_interfaces_20261124/`](paper_interfaces_20261124/)）

以下 3 个 `.lean` 文件自 `epi_work` 归档至此隔离区，对应分轨 `2A`/`2B`/`2C` 的章节 ↔ 模块映射与代表性 `#print axioms`：

| 文件 | 定位与公理情况 |
| :--- | :--- |
| [`Paper2A.lean`](paper_interfaces_20261124/Paper2A.lean) | Paper 2A 代表性接口（仅基础三公理） |
| [`Paper2B.lean`](paper_interfaces_20261124/Paper2B.lean) | Paper 2B 代表性接口（仅基础三公理；显式说明 `thm:finite-state-tail` 需要 Perron–Frobenius 正特征向量作为外部参数） |
| [`Paper2C.lean`](paper_interfaces_20261124/Paper2C.lean) | Paper 2C + T6 临界标度草案接口：**含 1 条项目自加公理 `C_S_pole_decomposition`**（对应论文中 `lem:pole` 的极点分解，未入 Lean 内核）与内核已证的 `scaling_function_identity`。正因其含新增 `axiom`，不可直接放入 `epi_formal/EpiFormal/`。 |

## 二、已被取代的历史草案（`superseded/`）

| 文件 | 状态 |
|---|---|
| `superseded/ResidueUpper358_Draft.lean` | 已被取代（2026-11-23）：骨架 + 2 处 `sorry`。取代者为通用框架 `EpiFormal/ResidueCertGenBase.lean` + `ResidueCertGen/` + `ResidueCertGenSound.lean` + `ResidueCertTable.lean`，见 `verification/cert_v3_redesign_20261123.md` |
| `superseded/ResidueCertChunk0_Draft.lean`、`superseded/ResidueCertData41179_*.lean` | 已被取代：原在 `epi_formal/EpiFormal/` 下，因 `h_hi` 对 `i` 全量化（约 $3.4\times 10^7$ 情形）无法通过；移出以免 `lake build` 的 `EpiFormal.+` glob 编译失败 |
