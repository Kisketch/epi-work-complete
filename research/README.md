# 研究笔记与阶段规划档案（`research/`）

> 本目录归档除两篇主论文外的新兴研究线与阶段性研究规划，均严格遵守 [`../AGENTS.md`](../AGENTS.md) 诚实分类与边界声明：**本目录下任何内容均不声称证明 $e+\pi$ 无理性。**

## 一、活跃研究方向

| 文件 | 主题 | 当前核心结论与边界 |
| :--- | :--- | :--- |
| [`kahane_q6_note_20261125.md`](kahane_q6_note_20261125.md) | **Kahane 公开问题 Q6**（幂次模 $1$ 覆盖集局部维数） | 证明了**几乎每个**随机目标序列的上界（定理 2）与淬火弱下界（定理 3），并将 §3c′–§3c‴ 归约为引理 R ⇒ 猜想 D′ ⇒ 引理 D（注：**原笔记冻结保留，猜想 D′ 与引理 R 的反例否证见下述 Addendum**）；伴随 Fourier / 鞅数值探针见 [`../verification/kahane_lemmaD_fourier_20261125.py`](../verification/kahane_lemmaD_fourier_20261125.py) 等 5 组脚本 |
| [`kahane_q6_addendum_20261125.md`](kahane_q6_addendum_20261125.md) | **Kahane Q6 增补与确定性局部下界（Round 2 新突破）** | ① **彻底否证**原笔记猜想 D′ 与引理 R（含 $2\varepsilon\in\Q$ / $v\mid h$ 构造），同时证明最优 $m\asymp n^{1/3}$ 包络为 $\exp(-c n^{2/3})$，故**引理 D 仍开放**；② 无条件证明对**一切**确定序列 $(b_n)$ 成立的局部维数下界 **定理 K-1 / K-2**：$\underline{\dim}_{\mathrm H}(E(\varepsilon),M)\ge\frac{\log(\lceil 2\varepsilon M\rceil-1)}{\log M}$（严格 $2\varepsilon M>K\ge 3$），经 [`../verification/verify_kahane_q6_refutation_and_det_20261125.py`](../verification/verify_kahane_q6_refutation_and_det_20261125.py)（最高 `dps=32000`, $n=45000$）全部核验通过 |

## 二、2026-11-24 阶段规划与总览归档（[`planning_20261124/`](planning_20261124/)）

以下 5 份规划文档自本地主检出根目录整理迁入 `planning_20261124/`，作为研究决策轨迹留痕（非数学证明）：

- [`master_overview_20261124.md`](planning_20261124/master_overview_20261124.md)：2026-11-24 全工作区状态、T6 临界标度升级与两主稿拆分总览；
- [`development_plan_20261124.md`](planning_20261124/development_plan_20261124.md)：早期形式化收尾与五项延展独立规划；
- [`integrated_advancement_plan_20261124.md`](planning_20261124/integrated_advancement_plan_20261124.md)：合并推进执行路线图；
- [`PI_新努力方向与路径_20261124.md`](planning_20261124/PI_新努力方向与路径_20261124.md)：方向与路径原始规划备忘；
- [`paper2_split_plan_20261124.md`](planning_20261124/paper2_split_plan_20261124.md)：论文二拆分方案（v1 三轨一补与 v2 两主稿打包）。
