# 论文二 `tab:residues-general` 全表 Lean 内核核查（2026-11-23）

**一句总判断**：论文二表 `tab:residues-general`（$m\in\{2,\dots,6\}$, $r\in\{1,m\}$，N=512）的 10 个区间、上下界共 20 个单侧证书，其**整数层**全部在 Lean 内核中通过（201/201 模块，`decide +kernel`，无 `native_decide`）；从整数层到 $\dim_H F_{m,r}$ 闭区间的**通用可靠性定理**与 20 个实例、5 条严格分离也已编译通过，27 条新声明只依赖 Lean 三条基础公理（§3）。**它没做到的是**：区间的严格性（开区间）仍依赖论文中引用的压力理论（CLU 的 Bowen 公式），未形式化；这些结果与 $e+\pi$ 的无理性无关，对原问题无推进。

## 1. 架构

| 层 | 文件 | 内容 |
| :--- | :--- | :--- |
| 通用检查器（core Lean） | `epi_formal/EpiFormal/ResidueCertGenBase.lean` | `cellAt`（闭式格公式）、`antiOK`、`rowSum`、`powU/powL`（指数清除的幂包络）、`rowU/rowL`、`allU/allL`、`vecOK`、`tailU/tailL` |
| 证书数据（core Lean，生成） | `epi_formal/EpiFormal/ResidueCertGen/M<m>R<r><L/U>{,C0..C7,All}.lean` | 每证书：参数 + 512 维单调向量 + 8 个 64 行分块 + 汇总；定理 `vec_ok`、`tail_ok`、`ok<c>`、`tab_ok` |
| 通用可靠性（Mathlib） | `epi_formal/EpiFormal/ResidueCertGenSound.lean` | `dimH_le_of_certU`、`le_dimH_of_certL`：布尔检查为真 ⇒ 维数界；经 `step_cert_upper_sound` / `step_cert_lower_sound` 与 `enclose_rpow_upper/lower` |
| 实例与汇总（Mathlib，生成） | `epi_formal/EpiFormal/ResidueCertTable.lean` | 20 个单侧界 + 5 条严格分离 $\dim_H F_{m,m}<\dim_H F_{m,1}$ |
| 生成器 | `verification/emit_cert_gen.py` | 每项 Lean 检查先在 Python 精确整数中镜像断言；最小余量与 `certify_side` 精确相等 |

关键观察：20 个证书的试探向量全部单调不增（Python 断言 + Lean `vecOK`），故像格上的最大/最小值即端点值，无需 max/min 表；这把原 v2 设计中约 3.4×10⁷ 个 `decide` 情形降到每证书约 6.6×10⁴–1.3×10⁵ 个整数检查。

## 2. 整数层实测（已核实）

- 日志：`verification/lean_check_certgen_core_20261123.log`；生成日志：`verification/emit_cert_gen_20261123.log`。
- 201/201 EXIT 0；累计约 1368 s；峰值 RSS 1.9 GB；Lean 4.35.0，Linux 沙箱，纯 core（不导入 Mathlib）。
- 源文件 SHA256（`ResidueCertGenBase.lean` + `ResidueCertGen/*.lean` 串接）：`7bd574ec…9e12a76`，与检查副本一致。

## 3. Mathlib 层实测（已核实）

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| `ResidueCertGen.dimH_le_of_certU` / `le_dimH_of_certL`：布尔检查为真 ⇒ $\dim_H F_{m,r}\le s$ / $\ge s$（任意参数） | 无条件结果（形式化的可靠性定理） | **已核实**：`lake build` EXIT 0；公理 = Lean 基础三公理 | 把论文 `thm:residues-general`(ii) 的整数证书判据落到可执行检查器 | `audit_residue_cert_20261123.log` |
| `ResidueCertTable.{le_dimH_F,dimH_F_le}{21,22,31,33,41,44,51,55,61,66}`：表中 20 个单侧闭界 | 有限计算（只覆盖这 10 个集合） | **已核实**（同上；0 `sorry`，0 `native_decide`） | 复现并形式化 `residue_certificate_general_N512.py` | 同上 |
| `ResidueCertTable.dimH_F{mm}_lt_F{m}1`（m=2..6） | 有限计算 | **已核实**（同上） | 论文 `thm:residues-asymptotic` 对全部 $m\ge2$ 已有分析证明（作者自报 Lean 已闭合）；此处为数值独立复核 | 同上 |
| 区间严格性（开区间） | 条件于 CLU Bowen 公式（引用） | 未形式化 | 论文 `thm:residues` 证明中的压力论证 | 论文正文 |

- 构建：Lean 4.35.0 + Mathlib v4.35.0（`lake-manifest.json` 锁定版本），`LEAN_NUM_THREADS=1 lake build EpiFormal.ResidueCertTable` EXIT 0（含 200 个证书模块与 51 个依赖模块）。
- 独立审计入口：`epi_formal/AuditResidueCert.lean`（27 条 `#print axioms`），**未并入**主 `Audit.lean`（937 条双射保持不变）；`verification/check_audit_reconcile.py` 复跑 ALL PASSED（逃逸关键字扫描覆盖新增文件，0 命中）。
- 尝试过但放弃：用内侧点 $s\mp1/2048$、$s\mp1/4096$ 直接在 Lean 里证明开区间——N=512 时余量为负（$F_{4,1}$ 上侧：−1.6×10⁻³、−6.8×10⁻⁴），需要更细网格。

## 3b. 论文修改

- `paper2_spectral_gap_dimension/patch_residues_N512_20261123.py` 同步修改主 tex 与拆分源（`sec-windows`、`sec-resasymp`、`intro-2C`、`intro-shared`、`frontmatter`、`frontmatter-2C`、`sec-preface`）：`thm:residues` 上界 359/512 → 179/256，证明改为 512 网格（K=130、$2^{80}$ 子字母表、新的精确余量），`tab:residues-general` 换成 N=512 数据（10 个区间宽度均为 1/512），新增 `rem:residue-kernel` 说明 Lean 闭区间与未形式化的严格性。
- tectonic 0.15.0 重编：主论文 58 页、2C 拆分稿 21 页，0 未定义引用；日志 `paper2_spectral_gap_dimension/paper2_build_tectonic_20261123.log`。tectonic 与 MiKTeX 字体度量不同，存在若干 Overfull `\hbox`（基线版本同样存在），以作者本机 MiKTeX 结果为准。

## 4. 文献关系（负搜索口径）

- 2026-11-23 两组英文网页检索（"formally verified Hausdorff dimension bounds continued fraction Cantor set Lean Coq Isabelle certificate"；"rigorous computation Hausdorff dimension continued fractions restricted digits transfer operator computer-assisted proof Mathlib"）：**负搜索未找到**证明助手内核检查的连分数康托集维数数值界先例。检索到的相关工作为计算机辅助严格数值（Jenkinson–Pollicott，arXiv:1611.09276；Pollicott–Vytnova，Trans. AMS Ser. B 9 (2022)，期号页码**未核到**），均非形式化证明。覆盖范围仅限上述网页搜索，未查 zbMATH/MathSciNet、Lean Zulip 归档、Coq/Isabelle AFP 全库。
