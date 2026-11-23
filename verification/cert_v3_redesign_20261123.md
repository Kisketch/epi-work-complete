# N=512 残差证书（m=4, r=1, s=179/256 上侧）Lean 内核核查：chunk0 卡点诊断与 v3 重设计（2026-11-23）

**一句总判断**：chunk0 失败的根因是 `cert_h_hi` 的命题形状（每个 (j,k) 都对全部 i∈range 512 做量化，约 3.4×10⁷ 个 `decide` 情形）以及在 elaborator 端用 `decide` 求值；改成"单调性 + 闭式格公式 + `decide +kernel`"后，**证书的整数层**（512 行严格不等式 D1 + 66,560 个系数上界 E1 + 尾界 + 向量单调）在纯 core Lean 中 41.8 秒全部通过，公理至多 `propext`。**它没做到的是**：从这些整数事实到 $\dim_H F_{4,1}\le 179/256$ 的实分析桥接（rpow 包络引理实例化、`step_cert_upper_sound` 接线）仍未完成，所以该维数上界的 Lean 形式化**还没有闭合**。

## 1. 诊断

| 现象（原日志） | 根因 |
| :--- | :--- |
| `lake_check_chunk0*.log`：`maximum recursion depth`（L11、L29） | `decide` 先在 elaborator（`Meta.whnf`）里求值 `Decidable` 实例，深递归；与数据规模叠加即爆 |
| 同上：`get1 certCellLC0` 类型不匹配 | 该日志早于 `f7b39ae`（get2 修正），属历史错误；当前文件已改用 `get2` |
| `cert_h_hi_c0` 设计规模 | `∀ j∈range 512, ∀ k∈range 130, ∀ i∈range 512` 共 512·130·512 ≈ 3.4×10⁷ 情形（映射文档设计口径为 "66k 格"，两者不符） |

## 2. v3 的数学依据（Python 精确断言，见 `emit_cert_core_v3.py`）

1. 试探向量 `v`（512 个正整数）**单调不增**：511 处相邻比较零违例。
2. 每格 `[l, r]` 满足 `l ≤ r`、宽度 ≤ 2（总宽 66,846 / 66,560 格），且 `l = min(511, 512² // ((4k+1)·512 + j + 1))`、`r = cell(a, j)`。
3. 由 1–2，`max v[l..r] = v[l]`，所以 v2 的 `maxV` 矩阵与 `h_hi` 命题可整体去掉，`cellL/cellR` 用闭式公式在 Lean 中定义而非存数据。
4. 用 v3 公式重算的最小相对余量与原 `certify_side(4,1,179/256,"upper")` **精确相等**（`Fraction` 恒等断言），数值 2.738737×10⁻⁴。

## 3. Lean 内核实测（本机：Linux 沙箱，Lean 4.35.0 core，不导入 Mathlib）

文件：[`epi_formal/EpiFormal/ResidueCertCoreV3_0_512_Draft.lean`](../epi_formal/EpiFormal/ResidueCertCoreV3_0_512_Draft.lean)（生成物，SHA256 `da13db31…7b0e`，未被 `EpiFormal.lean` / `Audit.lean` 导入）。日志：[`lean_check_core_v3_20261123.log`](lean_check_core_v3_20261123.log)。

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| `vec_anti`：向量单调不增 | 有限计算（只覆盖这 512 个数） | **已核实**（`decide +kernel`；公理：`propext` = Lean 基础公理） | 证书内部引理 | 日志 |
| `row0…row511`（D1）：Σₖ hiₖ·v[cellL k j] + tailU·v₀ < SCALE·vⱼ | 有限计算 | **已核实**（`row0` 公理仅 `propext`；全文件 0 error、0 `sorry`/`native_decide`/`axiom`） | 复现 `residue_certificate_general_N512.py` 上侧证书 | 日志 |
| `hiok0…hiok511`（E1）：hi¹²⁸·(a·512+j)¹⁷⁹ ≥ SCALE¹²⁸·512¹⁷⁹，66,560 格 | 有限计算 | **已核实**（`hiok511` 零公理） | 即 `enclose_power` 的整数判据（未约分形式，与约分形式等价：两边同乘 g¹⁷⁹） | 日志 |
| `tail_ok`：ustart 为 SCALE·517^(−51/128) 上界且 tailU·4·51 ≥ ustart·128 | 有限计算 | **已核实**（零公理） | 尾积分界的整数部分 | 日志 |
| $\dim_H F_{4,1}\le 179/256$ 的 Lean 闭环 | 无条件结果（论文二自报） | **未闭合**：缺 rpow 包络引理到 `hcert` 的实例化与桥接 | — | `论文二拆分分类与Lean精准映射_20261123.md` §路线 |

负对照（临时副本，未保留）：`hi0[0]×1000` → `row0` 被拒；交换 `v[0], v[1]` → `vec_anti`、`row0` 被拒；`hi5[1] := 最小合法上界 − 1` → `hiok5` 被拒；`hi5[1] − 1`（存储值有 1 的合法松弛）→ 正确接受。

资源：全量单文件 41.8 s、峰值 RSS 约 2.8 GB；128 行分块约 7.7 s、约 1.1 GB（原 Windows 机器建议分块：`python verification/emit_cert_core_v3.py 0 128` 等）。

## 4. 下一步（桥接，按依赖顺序）

1. 在 Mathlib 侧写一个"布尔检查 → 命题"的转换引理：`rowOK j hi = true → (实数行不等式)`，`hiOK = true → ∀k, SCALE·((a·512+j)/512)^(−179/128) ≤ hiₖ`（后者用已验证的 rpow 包络引理）。
2. 由 `vec_anti` 推出 v2 草案中的 `h_hi`（`max v[l..r] = v[l]`），替换 `verification/lean_drafts/ResidueUpper358_Draft.lean` 中对应 `sorry`。
3. 核心 Lean 证书文件被 Mathlib 文件导入时注意命名空间 `ResidueCertV3`，并在 `Audit.lean` 登记新声明后重跑 `check_audit_reconcile.py`。

旧草案 `ResidueCertChunk0_Draft.lean` / `ResidueCertData41179_*_Draft.lean` 由本方案取代，未删除，留作留痕。

## 5. 后续（同日）：v3 专用版已被通用框架取代

- 单一大 `decide` 合并检查在 3.9 GB 机器上被 OOM 杀掉，改为 64 行分块。
- 随后把方案推广为参数化通用框架：`EpiFormal/ResidueCertGenBase.lean`（通用布尔检查器）+ `EpiFormal/ResidueCertGen/`（20 个证书 × 10 个模块，由 `verification/emit_cert_gen.py` 生成）。论文表 `tab:residues-general` 的 10 个区间、上下界共 20 个单侧证书，其整数层全部在内核通过，见 `verification/lean_check_certgen_core_20261123.log`（201/201 EXIT 0）。
- `emit_cert_core_v3.py` 与 `ResidueCertCoreV3_0_512_Draft.lean` 已删除（git 历史 `639a620` 可取回）；旧草案 `ResidueCertChunk0_Draft`、`ResidueCertData41179_*`、`ResidueUpper358_Draft` 移至 `verification/lean_drafts/superseded/`。
