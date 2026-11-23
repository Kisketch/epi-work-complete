# Lean 草案隔离区（不进构建、不进审计）

> 本目录文件**不在** `epi_formal/` 内，故 `lake build` 与
> `verification/check_audit_reconcile.py`（全库 escape 关键字扫描）均不受影响。

| 文件 | 状态 |
|---|---|
| `superseded/ResidueUpper358_Draft.lean` | 已被取代（2026-11-23）：骨架 + 2 处 `sorry`。取代者为通用框架 `EpiFormal/ResidueCertGenBase.lean` + `ResidueCertGen/` + `ResidueCertGenSound.lean` + `ResidueCertTable.lean`，见 `verification/cert_v3_redesign_20261123.md` |
| `superseded/ResidueCertChunk0_Draft.lean`、`superseded/ResidueCertData41179_*.lean` | 已被取代：原在 `epi_formal/EpiFormal/` 下，因 `h_hi` 对 i 全量化（约 3.4×10⁷ 情形）无法通过；移出以免 `lake build` 的 `EpiFormal.+` glob 编译失败 |
