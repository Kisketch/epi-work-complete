# farey-gap 集成记录（2026-11-21）

> 一句总判断：`DenominatorCertificate.lean`（4 声明，namespace EpiCertificate，原 04_formalization_audits 工作拷贝，原样入库）经复验后合入，全量审计 **493 条（489+4）、`sorryAx = 0`**；论文一 triage 4 项自报（两 bridge、dirichlet-divisor、farey-gap）至此**全部清零**。

## 一、复验（主会话亲手）

- 文件 4,416 字节，UTF-8 无 BOM，`sorry/admit/axiom` 零命中（注释行仅提纪律），4 个定理。
- import 闭包：Mathlib 分片（Pi.Bounds / ExponentialBounds / Tactic）+ `EpiFormal.AdjacentWitness`（主树已有）。
- `lake env lean` 复验 EXIT 0（`farey_verify_20261121.log`）：4/4 纯基础三公理；正文"四声明仅基础公理"声称转正。

## 二、合入与审计

- 拷贝入库（内容零改动）；`EpiFormal.lean` +1 import；`Audit.lean` +1 import + 4 条 `#print`。
- 单目标构建 EXIT 0；全量审计 `audit_farey_wired_20261121.log` EXIT 0：493 条，`sorryAx` 0，error 0，EpiCertificate 4 条全在。
- 白名单总数不变（仍 22）。

## 三、口径

- 论文一自报 4/4 清零：`conditional-bridge`、`ai-reduction`（桥接审计）、`dirichlet-divisor`（DVerify 13 条）、`farey-gap`（EpiCertificate 4 条）。
- 本记录只覆盖有限分母证书；`prop:finite-match` 等应用链仍为纸面（triage 原表）。
