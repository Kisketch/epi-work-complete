# 存量审计报告（e+π 项目 + 第二阶段谱隙/维数）

日期：2026-11-16
审计立场：Lean 内核验证只排除攻击 1/3/7 在推导步骤层的触发，不排除攻击 2/4/5/6 在命题陈述/解释层的触发。故已过内核的 claim 仍逐条做后四类攻击。
MAY-ASSUME 列表：经典定理（Lindemann–Weierstrass、Nesterenko 1996、Gelfond–Schneider、Roth、Hurwitz/Perron、Eggleston、Bugeaud–Liao–Rams、Kraaikamp–Liardet、BDS）+ 两条 δ 公理（deltaSel_tendsto_zero、abs_deltaSel_lt，经典 e 连分数误差估计，mathlib v4.35 无 e 展开定理）。

---

## A. 已有成果清单（claim → 依赖）

### 第一阶段（e+π，机器验证）
- C1 Vieta：e+π 与 eπ 至少一个超越。依赖：e,π 超越（公理）+ 二次根代数。
- C2 六配对：e±π,eπ,e/π 至多一个有理。依赖：C1 + 域运算。
- C3 测度归约：任一组合有理 ⇒ μ(π)=2。依赖：μ(e)=2（公理）+ Möbius 不变性。
- C4 Meiburg Flint Hills 情形：μ(π)<5/2 ⇒ Flint Hills 收敛。依赖：π 超越 + 计数引理（已定理化）。
- C5 Alekseyev 方向：Flint Hills 收敛 ⇒ μ(π)≤5/2。依赖：π 超越 + 最近整数论证。
- C6 分类格（theorem2_classification）：j‖Q_j x‖→0 ⇔ x∈L=ℤ+ℤ(e+1)/2。依赖：δ 两公理。
- C7 间隙（corollary3_gap）：x∉L ⇒ ∀c<1/4, ¬(最终 j‖Q_j x‖≤c)。依赖：C6 + defect 引理。
- C8 Dj 归约链（EscapeReduction）：D_j(B)=0 最终 ⇒ Bπ∈L。依赖：C7 + 尖锐界 1/8。
- C9 P1⇒e+π 无理（条件）。依赖：C8 + 三等价。前提 P1 开放。

### 第二阶段（谱隙/维数）
- S1 apprExponent_eq_zero_iff：Λ(x)=0 ⇔ j‖Q_j x‖→0。依赖：limsup 定义（仅基础公理）。
- S2 spectral_gap：Λ(x)=0 或 Λ(x)≥1/4。依赖：S1 + C6 + C7。
- S3 levelSet_below_eq_lattice：c<1/4 ⇒ {Λ≤c}=L。依赖：S2 + C6。
- S4 latticeL_countable：L 可数。依赖：ℤ² 可数（仅基础公理）。
- S5 dimH_levelSet_below：c<1/4 ⇒ dimH{Λ≤c}=0。依赖：S3 + S4 + 可数集维数0。
- D1 Qsel_ge_factorial：Q_j≥j!（j≥1）。依赖：Qsel 递推（仅基础公理）。
- D2 Qsel_succ_le：Q_{j+1}≤(4j+3)Q_j。依赖：Qsel 递推 + 单调（仅基础公理）。
- D3 fiber_card_le：分支数≤⌊16t⌋+1（对 j,c 一致）。依赖：D2 + 单射计数（仅基础公理）。
- T-finite（**2026-11-18 已机器验证**，DimHFinite.dimH_levelSet_finite）：一切实数 c，dimH{Λ≤c}=0。依赖：D1+D3 + 存活中心 Finset 递归 + 周期性 + Hausdorff 判据（**仅基础公理，不依赖 δ 公理**）。原 4 个 GAP 全部闭合，见下。
- Conj（猜想）：权重相变 α<1 维数1，α≥1 维数0。开放。

---

## B/C. 逐条敌意审查 + 判决

### C6 分类格（核心依赖，重点审查）
1. 步骤不推出：内核验证 ✓。但陈述是 j‖Q_j x‖→0（趋于0），不是 limsup=0 的 ENNReal 形式——S1 已 bridging，需确认 bridging 正确（见 S1）。
2. 假设未满足：依赖 δ 两公理。δ_j=Q_j e−P_j→0 与 |δ_j|<1/(2jQ_j) 是经典 e 连分数事实，但**作为公理引入，未机器验证**。[标注：公理化，非机器验证]。这是 MAY-ASSUME 内的，合规，但下游所有依赖 C6 的 claim 都继承此公理依赖。
3. 小情形：x=0∈L（m=n=0），j‖Q_j·0‖=0→0 ✓。x=(e+1)/2∈L，数值 j≥10 <1e-12 ✓。x=1/2∉L？需确认 1/2∉L：1/2=m+n(e+1)/2 ⇒ 若 n=0 则 m=1/2∉ℤ；n≠0 则 e=(1−2m)/n−1∈ℚ 矛盾。故 1/2∉L ✓，应有 limsup≥1/4。
4. 同义反复：C6 不是 e+π 无理性的改头换面。它是关于逼近指数零集的刻画，独立命题。✓
5. 证明过多：骨架是「j‖Q_j x‖→0 ⇒ defect 最终0 ⇒ x∈L」。套到 π'=A/B−e：π' 使 e+π'=A/B∈ℚ。C6 对 π' 是否成立？C6 是关于任意 x 的逼近刻画，对 π' 也成立（π'∉L 一般），不矛盾。**关键**：C6 本身不证 e+π 无理，它只是刻画零集。✓ 无证明过多。
6. 错误解释：C6 刻画的是 {x:Λ(x)=0}，不是 {x:Λ(x)<∞}。后者更大。论文须区分。✓ 陈述正确。
7. 关键处手挥：内核验证，无手挥。✓
**判决：AUDIT-PASS（公理依赖已显式标注）**

### C7 间隙
1. 步骤不推出：陈述 ¬(最终≤c) 对所有 c<1/4。谱隙用其推 limsup≥1/4。衔接：limsup<c ⇒ ∃c'<c 最终≤c'（limsup 定义），与 C7 矛盾。故 limsup≥1/4。**此衔接在 spectral_gap 证明中通过 toReal+exists_between 显式完成**（已逐字核实 line 92-111）。✓
2. 假设未满足：c<1/4 严格。c=1/4 边界未覆盖（C7 只给 c<1/4）。谱隙结论 Λ≥1/4 含等号，正确（Λ 可以=1/4）。✓
3. 小情形：c→0 时 C7 退化为 C6 的 necessity（line 685-697 处理 c≤0）✓。
4. 同义反复：C7 是 C6 的定量强化，非目标改头换面。✓
5. 证明过多：C7 对 π'=A/B−e 成立（π'∉L ⇒ limsup≥1/4），不推出 e+π' 无理。✓
6. 错误解释：C7 给 limsup≥1/4，不是 limsup>1/4。等号情形开放（Λ=1/4 是否可达？未证）。论文不可声称间隙是开的 (1/4,∞]。✓ 陈述用 ≥ 正确。
7. 关键处手挥：内核验证。✓
**判决：AUDIT-PASS**

### S1 apprExponent_eq_zero_iff
1. 步骤不推出：Λ(x)=ofReal(limsup a_j)（ENNReal）。Λ=0 ⇔ limsup a_j≤0（ofReal 单射于非负）⇔ limsup=0（a_j≥0）⇔ a_j→0（非负序列 limsup=0 ⇔ 趋于0）。**关键衔接**：非负实序列 limsup=0 ⇒ 趋于0，需 a_j≥0（apprSeq_nonneg ✓）。内核证明用 limsup_le_iff + tendsto_nhds_zero（已核实 line 70-79）。✓
2. 假设未满足：a_j≥0 已证（apprSeq_nonneg）。✓
3. 小情形：x∈L 时 a_j→0，Λ=0 ✓。
4. 同义反复：否。✓
5. 证明过多：否。✓
6. 错误解释：Λ 用 ENNReal limsup，Λ=0 对应 limsup=0 而非"最终=0"。S1 正确区分（趋于0，非最终=0）。✓
7. 关键处手挥：内核验证。✓
**判决：AUDIT-PASS**

### S2 spectral_gap
1. 步骤不推出：by_cases x∈L。x∈L ⇒ C6 ⇒ a_j→0 ⇒ S1 ⇒ Λ=0。x∉L ⇒ 反证 Λ<1/4 ⇒ toReal L<1/4 ⇒ ∃c∈(L,1/4) ⇒ Λ<ofReal c ⇒ 最终 a_j<c（eventually_lt_of_limsup_lt）⇒ 最终 a_j≤c ⇒ C7 矛盾。**逐步已核实**。✓
2. 假设未满足：eventually_lt_of_limsup_lt 需 IsBoundedUnder autoParam，ENNReal 完备格自动满足（探针验证）。✓
3. 小情形：x=0∈L ⇒ Λ=0 ✓。x=1/2∉L ⇒ Λ≥1/4 ✓。
4. 同义反复：否。✓
5. 证明过多：对 π'=A/B−e，S2 给 Λ(π')≥1/4（若 π'∉L），不矛盾。✓
6. 错误解释：值域⊆{0}∪[1/4,∞]，含 ∞。正确。✓
7. 关键处手挥：内核验证。✓
**判决：AUDIT-PASS**

### S3/S4/S5 阈下水平集
1. 步骤不推出：S3 用 S2 二分：Λ≤c<1/4 ⇒ Λ≠≥1/4 ⇒ Λ=0 ⇒ x∈L。反向 x∈L ⇒ Λ=0≤c。✓ 内核验证。
2. 假设未满足：c<1/4 严格 ✓。
3. 小情形：c=0 ⇒ {Λ≤0}={Λ=0}=L ✓。
4. 同义反复：否。✓
5. 证明过多：否。✓
6. 错误解释：S5 只给 c<1/4 维数0，不给 c≥1/4。论文明确区分。✓
7. 关键处手挥：内核验证。✓
**判决：AUDIT-PASS（S3,S4,S5）**

### D1 Qsel_ge_factorial
1. 步骤不推出：归纳 Q_{j+1}≥(j+1)Q_j。Qsel_succ_ge_mul：j=1 时 2·1=2≤7 ✓；j≥2 时 Q_{j+1}=(4j+2)Q_j+Q_{j-1}≥(4j+2)Q_j≥(j+1)Q_j（4j+2≥j+1 对 j≥1）✓。归纳 Q_j≥j! ✓。内核验证。
2. 假设未满足：j≥1 ✓。
3. 小情形：j=1: 1!=1≤Q_1=1 ✓；j=2: 2!=2≤7 ✓；j=3: 6≤71 ✓。
4. 同义反复：否。✓
5. 证明过多：否（纯整数递推）。✓
6. 错误解释：Q_j≥j! 是下界，正确方向（覆盖论证需 Q_j 大）。✓
7. 关键处手挥：内核验证。✓
**判决：AUDIT-PASS**

### D3 fiber_card_le（重点审查，覆盖论证核心）
1. 步骤不推出：子中心 k' 满足 |c/Q_j−k'/Q_{j+1}|≤R ⇒ k'∈[A,B]，A=Q_{j+1}(c/Q_j−R), B=Q_{j+1}(c/Q_j+R)。B−A=2RQ_{j+1}≤16t。映射 k'↦⌊k'−A⌋₊ 单射（k' 整数，差≥1 ⇒ floor 差≥1），像⊆[0,⌊16t⌋]，故个数≤⌊16t⌋+1。**关键不等式 B−A≤16t**：R·Q_{j+1}=t·Q_{j+1}/(jQ_j)+t/(j+1)≤7t+t=8t（用 Q_{j+1}≤(4j+3)Q_j≤7jQ_j 对 j≥1）。故 2RQ_{j+1}≤16t ✓。内核验证。
2. 假设未满足：t≥0（ht）✓，j≥1（hj）✓，c∈ℕ（父中心非负）✓。**注意**：c 限定为 ℕ（非负整数中心），覆盖论证中 x∈[0,1] 时中心 k∈[0,Q_j] 非负 ✓。但若 x<0 或 x>1 需平移——论文须限定 [0,1] 或用周期性。[标注：覆盖论证须处理 x∈[0,1] 限定，见 T-finite 审查]
3. 小情形：t=0 ⇒ branchB=1，子中心唯一（k'=cQ_{j+1}/Q_j 若整数）✓。j=1: Q_1=1,Q_2=7，R=t/(1·1)+t/(2·7)=t(1+1/14)，B−A=2R·7=14t(15/14)=15t≤16t ✓。
4. 同义反复：否。✓
5. 证明过多：否（纯计数）。✓
6. 错误解释：分支数≤⌊16t⌋+1 是上界，对 j 一致。正确。✓
7. 关键处手挥：内核验证。✓
**判决：AUDIT-PASS（但下游覆盖论证须处理 x∈[0,1] 限定与路径编码）**

### T-finite 一切实数 c 维数0（2026-11-18 更新：已内核验证，AUDIT-PASS）

**更新判决：AUDIT-PASS。** `DimHFinite.dimH_levelSet_finite (c : ℝ) : dimH (levelSet (ENNReal.ofReal c)) = 0`
经 `lake build EpiFormal.DimHFinite`（9057 jobs 零错误）+ `lake env lean Audit.lean`（AUDIT_EXIT=0）验证，
`#print axioms` 逐字输出：`[propext, Classical.choice, Quot.sound]`。零 sorryAx，**不依赖 δ 两公理**。

四个 GAP 的闭合（对照下方原审查）：
- GAP-1 已闭合：弃 goodPath 常函数，改 survSet Finset 递归；card_survSet_le（基数界）与
  centerOf_mem_survSet（中心序列归属）均内核验证，仅基础公理。
- GAP-2 已闭合：tailSet 含 0≤x≤1；apprSeq_add_intCast（周期性）+ 整数平移 LipschitzWith 1
  + dimH_iUnion 可数并，内核验证。
- GAP-3 已闭合：hausdorffMeasure_le_liminf_sum 逐条件核验；hausdorffMeasure_tailSet_zero
  与 dimH_tailSet_zero 内核验证。
- GAP-4 已闭合：tendsto_powB_div_factorial_rpow 用 FloorSemiring.tendsto_pow_div_factorial_atTop
  + Real.rpow_mul 显式恒等式，无渐近记号；rad_le_factorial 用 D1。内核验证。

**组装中发现并修正的真实错误**（原审查未预见）：
(a) centerOf_mem_interv 初版假设 ‖Q_j x‖≤rad t j 比水平集条件强 Q_j 倍，接不上 {Λ≤c}；
    改为 j·‖Q_j x‖≤t。原审查第 2 条 [UNVERIFIED] 由此坐实为真缺口并修复。
(b) tailSet t 0 = ∅ 是假命题（j=0 时 apprSeq=0≤t）；并集限制 J≥1 修复。
(c) 助理曾误判 T-finite 为假命题（漏乘 Q_j），已撤回。

**更强结果**：原计划 c<1/4 分支复用 S5（继承 δ 公理）；现改为单调归约 c'=max c 0 +
纯覆盖论证统一处理一切 c，故 T-finite 完全脱离 δ 公理与分类定理。

以下为 2026-11-16 原审查记录（保留作审计轨迹，判决已被上方更新取代）：
1. 步骤不推出：覆盖论证骨架——{Λ≤c}⊆∪_J∩_{j≥J}A_j(t)，第 n 层分支≤(Q_J+1)B^{n-J}，直径≤2t/(nQ_n)，s-内容≤(Q_J+1)B^{n-J}(2t/(nQ_n))^s→0（因 Q_n≥n!）。**数学骨架正确**，但：
   - [GAP-1] 路径编码：goodPath 用 ℕ→ℕ 常函数表示，center_path_mem 的 zero 分支失败（中心路径非恒等常函数）。**这是已知的形式化缺陷，未修复**。
   - [GAP-2] x∈[0,1] 限定：fiber_card_le 的 c∈ℕ 要求中心非负。{Λ≤c} 含负数与 >1 的数，须用‖·‖的周期性归约到 [0,1]，或用可数并分解。纸面证明未显式处理。
   - [GAP-3] Hausdorff 覆盖判据对接：hausdorffMeasure_le_liminf_sum 需 ediam≤r_n→0 与有限覆盖索引。s-内容→0 需对每个 s>0 证 liminf=0，再推 dimH=0。未形式化。
2. 假设未满足：D1,D3 已 AUDIT-PASS。但覆盖论证的「x 落在某层区间」需 center_mem_interv（探针有，但依赖 center_path_mem 缺陷）。[UNVERIFIED：完整组装]
3. 小情形：c<1/4 时 T-finite 应与 S5 一致（维数0）✓。c=1/4 边界：{Λ≤1/4} 是否维数0？纸面论证给是，但 Λ=1/4 可达性未知，不影响维数上界。
4. 同义反复：**审查重点**。T-finite 是否悄悄假设了 e+π 无理？否——T-finite 是关于 Λ 水平集维数的度量命题，与 e+π 无理性独立。即使 e+π∈ℚ，T-finite 仍成立（Λ 的定义不依赖 e+π 无理性）。✓ 无同义反复。
5. 证明过多：**审查重点**。骨架套到 π'：T-finite 对任意 x 的水平集成立，不推出 e+π' 无理。✓ 但须确认覆盖论证不偷偷用了「π∉L」——T-finite 证的是 {Λ≤c} 维数0，对 c≥1/4 这个集合非空（含 L），维数0 不与 L 可数矛盾。✓
6. 错误解释：T-finite 给 dimH=0，不是「集合可数」。c≥1/4 时 {Λ≤c} 不可数但维数0（如 Cantor 集）。论文须区分维数0 与可数。✓ 陈述正确。
7. 关键处手挥：**触发**。纸面证明用「s-内容→0」一句带过，未展开 (n·n!)^{-s} 压过 B^n 的严格估计（需 log(n!)~n log n 的显式界，如 n!≥(n/e)^n）。[GAP-4：增长估计需显式化]
**判决：AUDIT-GAP（数学骨架可信，但有 4 个显式缺口：路径编码、[0,1]限定、Hausdorff对接、增长估计显式化。原则上可补，未补完前不得标机器验证或"已证"）**

### Conj 权重相变
**判决：OPEN（猜想，非 claim，不参与下游）**

### 第一阶段 C1-C9
C1-C5 内核验证，经典内容，AUDIT-PASS（公理依赖标注）。
C8 Dj 归约：内核验证，但**第4类攻击触发审查**——C8 是「D_j=0 最终 ⇒ Bπ∈L」，其逆否「Bπ∉L ⇒ D_j≠0 最终」结合三等价给「Bπ∉L ⇒ e+π 无理」。**这是换靶**：P1=∀B,Bπ∉L 与 e+π 无理同族难度（n≠0 情形是 {1,e,π} 线性关系）。C8 本身 AUDIT-PASS（推导正确），但**第6类攻击**：C8 不降低难度，论文已诚实标注「换靶不降难」。✓
C9 条件定理：前提 P1 开放，AUDIT-PASS（条件性已标注）。

---

## D. 未闭合义务清单（OPEN）

按优先级（2026-11-18 更新）：
1. **OBL-1：已闭合（2026-11-18）**。T-finite 完整 Lean 组装完成，四个 GAP 全部闭合，
   内核零 sorryAx，仅基础公理。DimHFinite.lean 已并入项目，Audit.lean 已追加打印。
2. **OBL-5（升为最高优先）**：δ 两公理的消除（形式化 e 连分数展开）。工程义务，非数学突破。
   注意：T-finite 已不依赖 δ 公理；仍依赖它们的是 C6/C7/S2/S3/S5/C8/C9（分类与谱隙链）。
3. **OBL-2**：Λ=1/4 可达性（间隙是否开）。开放，非必须。T-finite 给维数上界 0，
   不回答可达性；若 Λ=1/4 不可达则 {Λ≤1/4}=L（可数），若可达则不可数但维数 0。
4. **OBL-3**：权重相变猜想 Conj。开放，研究级。T-finite 坐实了 α=1 情形维数 0，
   为猜想提供了已验证的一半；α<1 维数 1 仍开放。
5. **OBL-4**：e+π 无理性（中心问题）。开放，P1 同族难度，无已知工具。

NEXT_PRIORITY：OBL-5（δ 公理消除）或 OBL-3（权重相变 α<1 半边）。
理由：OBL-1 已完成，第二阶段唯一新命题已坐实为机器验证定理。
OBL-5 是纯工程（mathlib 无 e 展开，需自建连分数理论），可消除分类链的公理依赖；
OBL-3 是真实数学推进方向（α<1 维数 1 需质量转移原理或 Eggleston 型构造）。
OBL-4 无工具（M17/M18 已审计确认），不应空转。

---

## 审计总结

- 所有机器验证 claim（C1-C9, S1-S5, D1-D3）：AUDIT-PASS（公理依赖显式标注）。
- **T-finite（2026-11-18）：AUDIT-PASS**。内核零 sorryAx，仅基础公理 [propext, Classical.choice, Quot.sound]。
  原 AUDIT-GAP 的 4 个缺口全部闭合；组装中另发现并修正 2 个真实错误（假设错配、假空集分支）。
- 无 AUDIT-FAIL（无明确反例或矛盾）。
- 中心问题 e+π 无理性：OPEN，无已知工具，禁止空转或声称解决。
- 诚实定位：第二阶段是经典谱隙现象的新实例 + 一个**已坐实**的新维数命题（机器验证）；非 e+π 突破。
  形式化≠新数学定理：覆盖论证是 Eggleston/BLR 型经典方法在具体实例上的严格化，
  新颖性在具体子列+权重+格+sharp 常数，不在方法。