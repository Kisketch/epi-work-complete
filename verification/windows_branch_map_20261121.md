# P2 stopped 柱树实例化：论文分支数断言 ↔ Lean 现货映射表（2026-11-21）

方法：只读 tex 加只读 Lean 源码 grep，不跑构建。tex 源 paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex；
Lean 源 epi_formal/EpiFormal/ 下各 lean 文件（行号为本次读取实测）。签名结论标已验证（只读），即本次亲眼读到源码；
未跑 lake build，故一切 Lean 结论均不含类型检查保证。
背景蓝图见 verification/windows_threshold_blueprint_20261121.md（其 D4 记录 b=2/b=1 摘要，S5 组装消费分支数）。

## 核查结论

两个矩形 coprime 计数核心（第一构造与第二构造的远多于 R² 部分）在 Lean 有显式常数下界对应；
R≍j / 远多于 j² / 远多于 j / ≥c₂j^{2γ} 代入桥、per-parent 单射（不同对给出不交子柱）、b=1 整数点计数下界在 Lean 完全缺失；
WindowLevelCount.level_count_ge 只给通用乘积形状（B_i 下界实例化文件自述留用方）；
WindowDescFiber 只有上界定理，方向与分支下界相反。

## A. 论文分支数断言（tex 精确摘录，全是下界）

| # | tex 行 | 精确表述（含常数/渐近/大O） | 下界还是精确数 |
|---|---|---|---|
| A1 | L2446 | R := T/u ≍ j（T := H_{j+1}，父柱分母 u） | 渐近关系（标度桥，供后代入用） |
| A1 | L2462 | = 0.0004/Z2 · R² + O(R log R)（矩形 RR 内 coprime 对数） | 下界方向（主项加误差的渐近下界） |
| A1 | L2464-2465 | 远多于 R² ≍ j² 个 coprime 对，uniformly for all large j | 下界 |
| A1prime | L2538-2539 | b=2（full-dimensional parity 构造）：每父远多于 R²、远多于 j² 个 children | 下界（质量分布组装输入） |
| A2 | L2526-2527 | 可选区间长度 (7/6)T/u星 ≍ j，给出远多于 T/u星、远多于 j 个 eligible choices of a | 下界（区间内整数点计数） |
| A2prime | L2539-2540 | b=1（prescribed-count 构造）：每父远多于 j 个 children | 下界（质量分布组装输入） |
| A3 | L2771-2776 | R = T/uprime ≥ c1 j^{1-eta log P} =: c1 j^g，g > 0，且 uprime = T/R < T | 下界（标度桥，显式指数 g） |
| A3 | L2784-2785 | 新矩形 Rprime_R 内对数 = (0.01x0.01)/Z2 · R² + O(R log R)，远多于 R² 且 ≥ c2 j^{2g} | 下界 |
| A3prime | L2822 | 每 stage-j 父至少 c2 j^{2g} 个 children（等条件质量推出 mu ≤ 连乘 c2^{-1}i^{-2g}） | 下界（显式常数 c2，显式指数 2g） |

注：per-parent 单射论证 tex 侧：第一构造 L2507-2512（删父前缀加末位 4 恢复 (m,n)，子柱内部不交）；
第二构造 L2817-2820（同理，另加固定 ell_j 个 ones 前缀）。


## B. 逐项核查（Lean 现货映射）

| 论文断言 | Lean 对应（文件:行，namespace 归属） | 签名/结论实测 | 判定 | 差什么 |
|---|---|---|---|---|
| A1 远多于R²计数核心 | EpiFormal/WindowMainBound.lean:166-167，namespace WindowMobiusCount（该文件 L9）；矩形定义 EpiFormal/WindowMobiusCount.lean:34-40（Mlo/Mhi/Nlo/Nhi = [0.34,0.36]x[0.20,0.22]，与 tex 一致） | theorem coprime_count_ge (R)(hR : 10^6 ≤ R) : R^2/10000 ≤ (copCount R)；L165 doc: at least R²/10000 | 已有对应（计数核心，显式常数 1/10000，阈值 R≥10⁶） | R=T/u≍j 桥、远多于j² 代入、per-parent 单射（tex L2507-2512）缺失；该文件自述 L25-28 明确 continuant 恒等式 t=mu+nv、不交性、Frostman 组装不在形式化范围 |
| A1prime 每父远多于R²远多于j² | 无直接引理（计数 copCount 是裸矩形成员数，未绑定到父柱 child 集） | 无 | 部分对应 | 计数核心有；父柱到矩形单射加 ≍j 代入完全缺失 |
| A2 区间长度恒等式 | EpiFormal/WindowAndResidueCore.lean:55-62 theorem thm18_prescribed_count_crossing | 结论为合取：a·u星+v星属于 [4T/3,5T/2] 且可选区间长度恒等于 7T/(6u星)（精确等式，非下界） | 部分对应（仅区间长度一半） | 区间长度到整数点个数下界（远多于T/u星的取整计数）、T/u星≍j 代入缺失；全库 grep 无 eligible/整数计数引理 |
| A2prime 每父远多于j | 无 | 无 | 完全缺失 | 无任何远多于j分支下界引理 |
| A3 远多于R²计数核心（新矩形） | EpiFormal/NoShortDimCount.lean:481-482，namespace NoShortDim（L10）；矩形定义 L31-40（MloS/MhiS/NloS/NhiS = [0.34,0.35]x[0.12,0.13]，与 tex L2781 一致） | theorem coprimeS_count_ge (R)(hR : 10^6 ≤ R) : R^2/100000 ≤ (copCountS R)（常数 1/100000，非最优，文件头 L23-25 自述下游只需远多于R²） | 已有对应（计数核心） | R≥c1j^g 桥、≥c2j^{2g} 代入、第二构造 per-parent 单射（tex L2817-2820）缺失；全库 grep 无 j^{2g} 引理 |
| A3prime/组装形状 | EpiFormal/WindowLevelCount.lean:19-27 theorem level_count_ge（通用：每父 ≥B j 且子互不交，则第 J 层总数 ≥ 连乘 B） | 纯组合引理，不含任何 C1i^b 实例 | 部分对应（形状） | 三档实例化（B_i ≥ C1i² / ≥C1i / ≥c2i^{2g}）缺失；文件头 L10-11 明示分支下界与对数渐近比较留用方 |
| （反向参考） | EpiFormal/WindowDescFiber.lean:42-46 theorem desc_card_le：后代数 ≤ 连乘 FmaxN（上界）；L23-39 desc_mem 仅成员保持 | 上界方向 | 对下界断言完全缺失（方向相反，仅可作对偶约束用） | 无下界 fiber 引理 |
| （树形状） | EpiFormal/WindowStoppedTree.lean：仅 nodup_of_children_disjoint（L45）加 mass_le_of_split（L81，上界） | 无分支下界 | 完全缺失 | per-parent 分支下界未形式化 |

记号（为避 shell 转义用 ASCII 替代）：Z2 = ζ(2)，g = γ，eta = η，P = φ，u星 = u_*，uprime = u 下一阶段，x = ×，属于 = ∈，签名中省略类型标注但结构与源码一致。


## 文档与实现的差异

1. NoShortDimCount.lean 文件头 L23 称主定理为 coprime_count_geS，实际源码 L481 定理名是 coprimeS_count_ge。以实测源码为准，引用时用后者。
2. 任务提示称 coprime_count_ge 位于 WindowMobiusCount：准确说全名是 WindowMobiusCount.coprime_count_ge，但定义位置在
   EpiFormal/WindowMainBound.lean:166（该文件开 namespace WindowMobiusCount），而非 WindowMobiusCount.lean
   （后者只含矩形定义与求和恒等式零件）。以实测为准。
3. 论文远多于记号（渐近下界）对 Lean ≥ R²/C（显式常数加阈值 R≥10⁶）：Lean 强于论文字面（去掉了大O记号），
   但阈值 10⁶ 是证明产物而非论文断言；R≥10⁶ 与 j 充分大的对应关系未建立（缺 R≍j 桥）。

## 无法核实项（本次只读、不跑构建，故以下均标未核到）

1. 上述 Lean 定理是否通过 lake build（各文件尾部的 print axioms 行仅是源码文本，未执行）。
2. R := T/u ≍ j（L2446）中 H_{j+1}/H_j = 4j+O(1) 上游是否在 Lean 有对应（超出本次 grep 范围，未上溯）。
3. 常数 c1、c2 的 tex 显式值（tex 只给存在性 c1>0 与笼统 c2，无数值；Lean 侧相应无）。
4. 输出文件不存在性已用 glob 确认（verification/windows_branch_map_20261121.md 写前无命中）。

