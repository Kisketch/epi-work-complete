# 论文二拆分方案：结构、理由、发展方向与评级（2026-11-24）

> **编制**：主会话（GLM-5.4 分析层）。**依据**：主稿逐节结构实测（本文件 §2，节选自当次结构盘点）、`split/` 实际文件形态、[`journal_landscape_20261124.md`](verification/journal_landscape_20261124.md)（E5，证据分级台账，主会话抽查 1 条通过）、T1 Bowen 清点、T2 施工图、T6 猜想草案、PI《新努力方向与路径》。
> **硬约束**：只增不减——原 63 页主稿与其 PDF **原样保留、永不改动**；拆分产物是**派生的独立投稿**，以补丁脚本与新文件实现；每一步经 `verify_repo_integrity.py` 与 `verify_paper2_merge.py` 核对。
> **评级性质**：所有分数是助理的判断，不是录用预测；期刊信息以 E5 的证据分级为准（部分条目有「未核到」字段）。

---

## 1. 现状盘点（实测）

- 主稿 4463 行 / 63 页，0 编译错误 / 0 未定义引用；`split/` 已有共享节库 `src_sections/`（28 个 .tex：sec-gauge 81.8KB、sec-windows 50.8KB、sec-poly 33.5KB、sec-resasymp 31.5KB、sec-gauge-core 39.2KB、sec-verification 21.7KB 等）+ 每轨变体（frontmatter-2A/2B/2C、intro-2A/2B/2C、prereq-2B/2C、sec-spectrum-2A、sec-num-2A）+ **四轨草案包装**（`2A_core_gauge_trichotomy/paper2A_draft.tex` 等各 ~1KB，均为 `\input` 列表 + MANIFEST）+ `BUILD_TRIAL_LOG.md`、`undef_ref_audit.py`。
- 声明页数：2A 24 页 / 2B 15 页 / 2C 24 页（`split/README.md` 口径；本轮未重编译验证）。
- **卫生项**：T1 提到的 `split/slice_index.csv` 实际不存在于 `split/`（本次 ls 证实）；索引缺失不阻塞拆分，但应新建一份真实索引（新文件）。

## 2. 主稿逐节地图（行区间为实测）

| 区块 | 行区间 | 内容（节选标题） | Lean 文件引用密度 |
|---|---|---|---|
| 引言/铺垫 | L168–416 | Introduction、Setup、Relation to prior work | 0 |
| **A1** 分类与初始谱隙 | L417–504 | Classification and initial spectral gap（2 thm） | 2 |
| **A2** 全谱离散化 | L505–621 | Complete spectrum discretization + step-function certificates（3 thm） | 10 |
| **A3** 有限能级零维 | L622–853 | All finite level sets have dimension zero…（2 lem 1 thm 1 cor） | 3 |
| **A4** 次临界权重与精确维数 | L854–1203 | Subcritical weights and exact Hausdorff dimensions（1 thm + 1 conj） | 7 |
| **A5** 临界能级与精确规范 | L1204–1663 | Critical levels and exact gauges（1 thm 2 cor） | 4 |
| **A6** 正能级三分法 | L1664–1843 | Three-way splitting at each positive level（1 thm） | 7 |
| **B1** 有限状态缺陷尾 | L1844–1995 | Finite-state constraints on defect tails（1 thm） | 4 |
| **B2** 多项式增长递推 | L1996–2542 | General polynomial-growth denominator recurrences（2 lem 3 thm 1 cor） | 5 |
| **B3** 任意增长商递推 | L2543–2881 | Universal extension to arbitrary growing-quotient recurrences（2 thm 1 cor） | 2 |
| **C1** 窗口约束维数 | L2884–3090 | Dimensions of CF window constraints（1 thm） | 0 |
| **C2** 短窗口与发散窗 | L3091–3340 | Short CF windows and divergent windows（2 thm） | 4 |
| **C3** 残差最终周期性 | L3341–3657 | Eventual periodicity of digit residues（2 thm 1 tab） | 3 |
| **C4** 预解恒等与全局分离 | L3658–3794 | Resolvent identity, global strict separation（1 thm 1 tab） | 0 |
| **C5** 多残差相变 | L3795–4052 | Multi-residue phase transition, Euler–Mascheroni 三阶渐近（1 thm 2 tab） | 16 |
| 数值证据 | L4053–4153 | Numerical evidence | 0 |
| 诚实声明与形式化验证 | L4154–4463 | Honesty statement, scope, formal verification | 36 |

## 3. 为何拆分（八条理由）

1. **篇幅**：63 页超出多数期刊舒适区；Adv. Math./TAMS 级单篇通常 ≤40 页。
2. **受众分离**：A 块对话分形几何/动力系统规范理论；B 块对话热力学形式体系与无限 IFS（E5：Banaji–Fraser、Kesseböhmer–Niemann 的 Adv. Math./TAMS 论文正是此类）；C 块对话度量丢番图与连分数数字约束（E5：ETDS/Nonlinearity 的 CF 例外集论文）。三个社群的审稿人、引用圈、术语都不同。
3. **风险分散**：巨稿一票否决风险集中在单一审稿过程；三篇独立评审互不拖累。
4. **成熟度不同步**：A 块已全内核闭环可先发；C 块等 T6 落地后分量最大；B 块等统一理论成文——拆分让每块按自己的节奏走。
5. **引用身份**：独立标题/DOI 便于被正确引用（巨稿常被含糊引用为「the arXiv paper」）。
6. **每篇以最强定理领队**：拆开后每篇开篇即其最硬结论，而巨稿的最强点会被稀释。
7. **只增不减的兼容性**：拆分=新文件+补丁脚本，原稿永不动，完全符合仓库宪章。
8. **审稿周期并行化**：三篇同时在不同刊手里排队，总等待时间远短于串行。

## 4. 拆分方案（目标结构；原稿保留为「完整版」）

| 目标稿 | 收录区块（主稿行号） | 现有轨文件 | 新增增量（全部追加式） | 声明页数 |
|---|---|---|---|---|
| **P2A 谱离散化与精确规范** | A1–A6（L417–1843）+ 引言节选 | `2A_core_gauge_trichotomy/`（draft + MANIFEST + sec-spectrum-2A/sec-num-2A 变体） | 无需新数学；定稿 frontmatter/摘要（含诚实清单：本篇覆盖的审计子集）；与 P2B/P2C 的交叉引用 | 24 |
| **P2B 一般递推与结构字母表理论** | B1–B3（L1844–2881）+ 引言节选 | `2B_general_theory/` | ①T2 施工图实施的统一理论：条件 (C1)–(C5)、结构字母表定义、统一维数定理与相变律（残差/多残差作推论回收）；②KMS 对照专节（PI 第 6 项）；③sofic 核最小推广（C5 层） | 15 → 预计 25–30 |
| **P2C 窗口、残差与临界相变** | C1–C5（L2884–4052）+ 引言节选 | `2C_windows_residues_finstate/` | ①**T6 临界标度**：猜想→定理（极点分解引理 + 隐式方程渐近，Layer A）；②超临界精确前因子（dκ/(2(2s₀−1))）入正文；③第四项探针与数值图谱（指向 S 轨） | 24 → 预计 28–32 |
| **S 数值与形式化补充** | 数值证据 + 诚实声明（L4053–4463） | `S_supplement/` | 扫描全表、标度验证表、Colab 复现纪律、证书管线说明；随 P2C（或独立 arXiv 补充） | 随母篇 |

**交叉引用纪律**：三篇各自引用「完整版」（原 63 页稿）作 companion long version；P2B/P2C 引用 P2A 的规范机器；**每篇的 Lean 声明只写本篇覆盖的审计子集**（988 条是全项目口径，不得让单篇暗示全部——这是 T1 发现的摘要口径问题的拆分版延伸）。每篇保留「不解决 e+π 开放问题」声明。

## 5. 打分评级（0–10；助理判断）

| 维度 | P2A | P2B | P2C | S |
|---|---:|---:|---:|---|
| 定理完备度（含 Lean） | 9.5 | 8 | 9 | 8.5（工具价值） |
| 新颖度（负搜索支撑） | 7.5 | 9 | 8.5 | 7 |
| 单篇自洽性 | 9 | 7（需统一理论补齐） | 8.5 | 随母篇 |
| 受众匹配与期刊纵深 | 7.5 | 8.5 | 8 | — |
| 增长空间（新方向注入） | 6 | **9.5** | **9** | 7 |
| 时效风险（低=分高） | 4 | 3 | 3 | 2 |
| **总评** | **A−** | **B+ → A+（统一理论落地后）** | **A− → A+（T6 落地后）** | 附件级 |

**一句话**：P2A 是最干净、最先能走的「精度之篇」；P2C 是临界相变故事的「完整之篇」，T6 是它的临门一脚；P2B 是最有希望定义「一般理论」的「纲领之篇」，天花板最高、风险也最高；S 是三篇共享的差异化卖点（严格整数证书 + 双机复现 + Layer A）。

## 6. 顶刊垫脚石分析（按杠杆大小排序）

1. **T6 临界标度律（服务 P2C）**：把「相变 + 双侧速率」补齐为「相变 + 速率 + 临界指数 1/2 + 标度函数 + 精确前因子」的完整临界现象叙事——这正是 Adv. Math./TAMS 上 phase-transition 论文（E5：Banaji–Kolossváry 的 countably many phase transitions、Kesseböhmer–Niemann 的压力零点谱）的完整形态。可行性：hard 但无需新范式（见 T6 §5）。**这是当前性价比最高的一块垫脚石。**
2. **结构字母表统一维数定理（服务 P2B）**：从「两族特例」升为「一般规律」；T2 已给出 (C1)–(C5) 定义候选与 20 步中的可复用部分（[MUL]/[GEN] 全部直接推广，[AP] 仅 6 处承重）。风险：一般尾的地板条件（调和和发散猜想）与 sofic 层需新数学。
3. **精确规范机器（P2A 供给 P2B/P2C）**：临界情形的「精确规范函数」问的答案要用它；P2A 先发建立可引用工具基座。
4. **全 Layer A + 双机复现纪律（服务全部）**：E5 显示该社区无人在做「维数结论全内核验证」——这是跨三篇的差异化标签，也是审稿人无法用「数值可能有误」攻击的护城河。
5. **负搜索纪律（服务全部）**：任何「无先例」表述注明检索范围（负搜索≠不存在），避免审稿反击。

**投稿排序建议**：P2A 先投（目标 ETDS / Nonlinearity，Adv. Math. 冲刺）→ P2C 带 T6 第二投（目标 Adv. Math. / TAMS）→ P2B 最后（目标 TAMS / Adv. Math.，引用前两篇）。此排序与 PI「arXiv 随段占位、期刊第二段后选档」的节奏一致。

## 7. 执行清单（全部只增不减）

1. 新建真实切片索引（`split/slice_index_20261124.csv`：节文件 | 字节 | 主稿定位），替代缺失的旧索引——不改任何旧文件。
2. 三篇 frontmatter 起草（标题、摘要、诚实清单、companion 声明）→ 以 patch 脚本进各轨 draft。
3. P2C：T6 定理化（先写极点分解引理的纸面证明 → Lean 陈述 → Layer A 审计）+ 超临界前因子小节。
4. P2B：(C1)–(C5) 定义节 + 统一定理陈述节 + KMS 对照节初稿。
5. 摘要口径补丁（自报 2 处 → 4 处，T1 发现）——补丁脚本留痕，PI 审后执行。
6. 每步提交前：`verify_repo_integrity.py` + `verify_paper2_merge.py` + `undef_ref_audit.py`。
7. 执行分工：frontmatter/初稿类 → muse-spark 执行者（待 PI 在 UI 里把「执行者」模型切到 muse-spark 连接后派发）；数学定稿与 Lean → 主会话。

## 8. 诚实边界

- 本方案不改变任何已证结论的状态；评级是助理判断；期刊纵深以 E5 的证据分级为准（含 6 条「未核到」字段）。
- T6 仍是猜想；统一理论未成文；「预计页数」是估计。
- 原稿 63 页版不因本方案有任何改动。

## 9. v2 修订：吸收外部深度调研（2026-11-24，PI 提供 code_artifact.html）

PI 另行提交了一份外部深度调研报告（桌面 `code_artifact.html`，《论文二冲刺数学顶刊深度调研与演进路径分析》）。主会话已通读并抽查其可核项：Banaji–Kolossváry 条目经 arXiv 页核实（Adv. Math. 449 (2024) 109735 ✓）；**报告还解开了论文 \cite{CLU} 的谜底**：CLU = Chousionis–Leykekhman–Urbański《On the dimension spectrum of infinite subsystems of continued fractions》（arXiv:1805.11904，主会话已打开核实 ✓）——这是等差数字母表方向的最近先例（它已证明算术级数/素数/平方数集的维数谱性质），T2 新颖性定位**必须**引用并与之区分：本仓库的推进在于渐近展开、相变律与临界标度，而 CLU 是谱的存在性/结构结果。

### 9.1 采纳的修订（两主稿打包，替代 §4 的三稿方案）

| 目标稿 | 内容 | 篇幅 | 第一志愿 | 第二志愿 | 保底 |
|---|---|---|---|---|---|
| **主稿 A = P2C 升级版**（多残差完整相变理论） | C1–C5 + **T6 临界定理**（临界指数 ½、标度函数、超临界前因子 dκ/(2(2s₀−1))）+ Chebyshev 严格界 + 内核附注 | 25–30 页 | Adv. Math. / Proc. LMS | ETDS / Math. Comp. | Forum Math. Sigma / Exp. Math. |
| **主稿 B = P2A+P2B 融合**（一般递推/结构字母表理论） | A1–A6 + B1–B3 + 统一理论（T2 施工图 (C1)–(C5)）+ KMS 对照节；**e 作为旗舰推论（Flagship Corollary）出现，不再作出发点** | 30–35 页 | Math. Ann. / Selecta | Trans. AMS / IMRN / Nonlinearity | JNT / Acta Arith. |
| **配套资产 = Lean 归档** | Zenodo/GitHub Release 独立 DOI + 一页复现指南 + 零 sorryAx 审计摘要；可选短文投 J. Automated Reasoning / ITP | — | 强背书附件 | — | — |

采纳理由：2B 单独 15 页体量偏轻；2A 单独有「e 特例化」风险（T1 审稿人会归为特殊常数案例）；合并后主稿 B 以一般理论面貌出现、分量达标。原 §4 的 P2A/P2B/P2C 独立稿方案**降级为备选**（若 PI 坚持三稿，仍可执行）。

### 9.2 采纳的合规与叙事修订

1. **发布节奏**：arXiv 挂出推迟到临界定理（T6）完成之后——用最强版本锁定优先权（外部报告建议，与 PI「期刊第二段后选档」兼容）。
2. **AI 合规**：Annals/Elsevier 2026 政策（外部报告引，政策原文未核到）要求 AI 使用声明——仓库已有 AI 贡献草稿（`03_submission_prep/`），按两主稿分别细化到「哪些思路/哪些证明 + 位置 + 人类作者责任」。
3. **去工程化叙事**：正文压缩审计工程语言为一段验证声明 + 归档指针；工程日志全部留在 verification/ 与 S 轨（与 T1 发现的摘要口径问题同向：不过度渲染也不漏报）。
4. **逐定理人工复核说明**：投稿前补齐（外部报告第④项）。

### 9.3 对标锚点（外部报告给出、主会话核对采纳）

- **Jenkinson–Pollicott 2018（Adv. Math. 325）**：转移算子严格界 + 计算机辅助验证可发 Adv. Math.——主稿 A 的直接模板；
- **DFSU 2020（arXiv:2007.10554）**：热力学形式体系摄动统一 Hensley/Good 渐近——T6 定理化的框架归宿；
- **Nakajima–Takahashi 2025（Adv. Math. 482）vs 同团队 JNT 2026**：「一般原理进 Adv. Math.，特定集合计算进 JNT」——主稿 B 必须跨过这道分水岭；
- **Wang–Wu 2021 / Kleinbock–Wang 2023**：可迁移抽象工具是 T1 审稿人的核心标尺。
（以上书目均来自外部报告转述，本轮未逐条打开核对——标注「未核到」；CLU 已核 ✓）

### 9.4 与外部报告的两处分歧（保留己见）

1. 外部报告认为「扩大数值精度/新特殊例子」是边际递减——**原则上同意，但例外是假设驱动的扫描**：本次临界扫描（334 点、零参数标度验证）正是第①项杠杆的实测前提，属于「先测分布再定机制」的必经步骤，不属于该警告范围。
2. 外部报告建议 2A 直接并入主稿 B——采纳，但**精确规范机器（A5）仍是 2B/2C 临界规范的工具供给者**，融合稿中应保留其独立定理地位而非降格为引理。

### 9.5 执行状态更新（flash 批次 v2 成果）

- E6/E7/E10 已交付并验收通过（[`flash_batch_v2_acceptance_20261124.md`](verification/flash_batch_v2_acceptance_20261124.md)）；E9 待补。
- 拆分的实际 tex 装配（两主稿包装）待：①T6 定理化；②PI 审阅 E10 补丁与三篇前言草案；③（可选）执行者切换 muse-spark 后派发装配任务。
