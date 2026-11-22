# dirichlet-divisor 合入记录（2026-11-21）

> 一句总判断：`DirichletDivisor.lean`（13 声明，namespace DVerify）经主会话亲手复验后合入，全量审计 **453 条（440+13）、`sorryAx = 0`**；论文一 triage 自报项 `prop:dirichlet-divisor`（tex 第 324 行"十条已审计"所指）至此在本工作区转正。

## 一、复验（主会话亲手）

- 文件 16,814 字节，UTF-8 无 BOM（头字节 `69 6D 70`），`^axiom` 零声明。
- `sorry` 全文件 1 命中 = 第 32 行中文注释纪律声明，非代码。
- `^(theorem|lemma)` 13 个（10 主 + Qsel_pos_all/H_le/H_lt 3 辅助）。
- `lake env lean` EXIT 0，自带 10 条 `#print` 全基础三公理（gcd_dvd_Qsel 仅 `[propext, Quot.sound]`）。

## 二、合入与审计

- `EpiFormal.lean` +1 import；`Audit.lean` +1 import + 13 条 `#print`。
- 单目标构建 EXIT 0；全量审计 `audit_dirichlet_wired_20261121.log` EXIT 0：453 条，`sorryAx = 0`，error 0，DVerify 13 条全在。
- 签名：基础三公理 410（+12）、双公理 19（+1）、白名单 22（不变）、单公理 1（不变）。

## 三、口径

- 转正的是引理本体（条件性必要条件 + 整除限制）；其在 `two-window`/`explicit-period`/`affine-window` 中的应用组装仍是纸面（下一攻方向）。
- 对真实 π 的 gcd 估计仍未获（稿件自承）；难度未降，仅筛法地基。
