# Cylinder Phase A 合入记录（2026-11-21）

> 一句总判断：连分数柱集基础设施 Phase A（continuant 矩阵＋收敛子递推）8 条定理合入，全量 568 条（560+8），`sorryAx = 0`，5 条基础三公理＋3 条零公理——L09/L10 的代数地基就位。

## 一、交付物

- `epi_formal/EpiFormal/Cylinder.lean`（`namespace Cylinder`）：cfMat/cfProd/cfMat_det/cfProd_det/convPair/convNum/convDen/cons 引理/nonneg。
- 接线：`EpiFormal.lean` +1 import（L32）；`Audit.lean` +1 import +8 prints。
- 日志：`verification/audit_cylinder_wired_20261121.log`（EXIT 0）。

## 二、设计决策

- 未采用 mathlib 广义连分数框架（GenContFract 重型无限理论，实例化成本高于自建）；自建 `List ℕ` 词上的 2×2 整数矩阵，det=(-1)^len，收敛子对递归——纯初等代数，零白名单。
- 坑：`let pq := ...` 阻断 rfl 定义展开→定义内联；`Int.ofNat_nonneg` 弃用→`Int.natCast_nonneg`；`EpiFormal.lean` import 行不相邻（L31/L3 分散），edit 前必读原文。

## 三、公理分布

- 8/8：5 × 基础三公理，3 × 零公理（convPair_cons/convDen_cons/convNum_cons 为 rfl/定义展开）。
- 全量 568 = 560 + 8；白名单总数不变。

## 四、下一步（Phase B）

柱集区间端点＋长度界（tex L2421–2425：端点 p_r/u、(p_r+p_{r-1})/(u+v)，长度 1/(u(u+v))∈[1/2u²,1/u²]），需 Möbius 单调性＋介值，服务 L02/L12/L13。
