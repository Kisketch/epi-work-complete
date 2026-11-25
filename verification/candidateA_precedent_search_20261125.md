# 候选 A 先例检索：在一般情形去掉 BLR 定理 7 的条件 (1.6)（2026-11-25）

**一句总判断**：候选 A 必须分成两半看。

- **线性情形** $f_n(x)=a_nx$：这正是论文二 2B 实际用到的情形。按我对 BLR 自己证明草图的阅读，这里没有失真项，条件 (1.6) 只是用来吸收误差，可以换成 $n=o(\log a_n)$。非阿基米德情形的同型公式已由 Fan–Fan–Ye（arXiv:2512.05690v1，引理 6.3）在**只有缺项条件、没有 (1.6)** 的前提下证明。因此线性半边属于"**方法已知**"，不能作为冲顶刊的新定理。
- **非线性情形**（例如 $f_n(x)=x^n$，$\delta_n\to0$，且 $\log f'_{n+1}/\log f'_n\not\to\infty$）：**负搜索未找到先例**。真正的困难在这里，即失真累积，以及每层分支数有界时的精确计数。

**连带发现一处引用错误**：论文第 2490 行（`rem:poly-BLR`）和第 2800 行（`rem:growing-BLR`）写道，BLR 的证明草图"表明 (1.6) 或可用 Baker 的插补技巧去掉"。这与 BLR 原文不符。我在 `paper2_venue_gap_assessment_20261125.md` 中沿用了这个错误说法，已在该文件中更正。

---

## 0. 检索范围

| 渠道 | 内容 |
| :--- | :--- |
| BLR 原文 | arXiv:1710.03596v1 的 TeX 源：定理 7（源码标签 `bad-general`）的陈述、条件，以及 §"Sketch proof" 全文逐字阅读 |
| 引用 BLR 的文献 | OpenAlex 列出 8 篇，Semantic Scholar 列出 9 篇（两者大部分重合）。其中 arXiv 上的 6 篇下载了 TeX 源做关键词 grep：1910.01437、1906.07995、1905.13644、2002.11607、2310.05528、2512.05690。Feng–Xu（Nonlinearity 2021）与 Zheng 的博士论文只看了题名 |
| arXiv API | 7 个检索式（§4），命中都与本问题无关 |
| WebSearch | 2 次（扩展 1 次、标准 1 次），未发现"对一切 $n$ 成立"型集合在一般 $\delta_n$ 下的维数公式 |

**未检索**：zbMATH / MathSciNet 引用链、Google Scholar；Kahane 2014、Pollington 1980、Baker 2015 的原文（只经 Fan–Fan–Ye 引言**转引**）。

---

## 1. BLR 定理 7 原文核对（arXiv:1710.03596v1，编号沿用此前核查记录）

- **集合**：$G(f,y,\delta)=\{x\in I:\lVert f_n(x)-y_n\rVert\le\delta_n,\ \forall n\ge1\}$，其中 $\delta_n<1/4$。
- **条件**：
  - (1.1) 是正则性条件 `cond-ext`：$\lim_{r\to0}\limsup_n\sup_{|x-y|<r}\log f_n'(x)/\log f_n'(y)=1$；
  - (1.5) 是 `hyp-1`：$\inf f'_{n+1}/\sup f'_n\cdot\delta_n\ge2$；
  - (1.6) 是 `hyp-2`：$\log f'_{n+1}(x)/\log f'_n(x)\to\infty$。
- **结论**：局部维数等于 $\liminf_n\frac{\log f_n'(v)+\sum_{j<n}\log\delta_j}{\log f_n'(v)-\log\delta_n}$。
- **(1.6) 在证明中的作用**（逐字阅读草图所得）：
  - **下界**：草图写出比值的下界 $\frac{\log f_n'(z)-\log f_1'(z)+\sum_{j<n}\log\delta_j+\sum_{j<n}\log(f_j'(z)^{-\gamma}/f_j'(z_j))}{\log2+\log f_n'(z_n)+\gamma\log f_n'(z)-\log\delta_n}$，接着写 "By (hyp-2), we have…"。也就是说，(1.6) 用来让累积的失真误差 $\sum_{j<n}\log(\cdots)$ 相对 $\log f_n'$ 可以忽略。
  - **上界**：同样有 $\prod_{j<n}f_j'(z)^{2\gamma}$ 型累积误差，草图写 "Therefore, by (hyp-2)…"。
- **Baker 插补的真实用途**：草图原文说，如果在某处 $f_n'$ "too sparse"，即 $\log f'_{n+1}\gg\log f'_n$，就借用 Baker 的办法（[Ba] 第 69 页），在 $f_n$ 与 $f_{n+1}$ 之间插入新函数 $\tilde f_m$（取 $\tilde\delta_m=1$），使比值不再过大，从而满足下界构造所需的 "estimate-righthand" 条件。所以插补处理的是**过稀疏**，用来保证下界的失真估计，**不是**去掉 (1.6) 的手段。

**【引用错误】**
- **位置**：论文第 2488–2491 行（`rem:poly-BLR`）与第 2798–2801 行（`rem:growing-BLR`）的末句。
- **原文写法**："whose proof sketch indicates that condition (1.6) may be removable by an interpolation device of Baker"。
- **核对结果**：BLR v1 草图把 Baker 插补用于处理过稀疏的情形（下界的 estimate-righthand）；(1.6) 在上下界中都被直接调用，草图中没有说它可以去掉。
- **建议改为**：
  > (Hypotheses as stated in arXiv:1710.03596v1, whose proof is given there only as a sketch.)

  也就是删去"(1.6) 或可去掉"的说法。
- 2026-11-23 核查（`paper2_novelty_review_20261123.md` 表格 R4 行）中"BLR 只在证明草图中提到用 Baker 插补去掉 (1.6)"同样不准确。该文件是历史记录，本次未改，以本条为准。

---

## 2. 线性情形：方法已知

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| 线性 $f_n(x)=a_nx$ 下不需 (1.6) 的 BLR 型公式（论文二 2B 的 $1-\alpha/r$、$\frac{1-\tau}{1+\tau\gamma_{\sup}}$） | 1（论文二已证，作者自报 Lean 闭合），但属于**方法已知** | 论文结论：已核（前两轮）；"方法已知"：本节判断 | **(a)** BLR 草图中的误差项在线性情形退化：$f_j'(z_j)=f_j'(z)$，可取 $\gamma=0$，剩下的只有每层"$\pm2$"取整与因子 2，累积为 $O(n)$。所以只要 $n=o(\log a_n)$，(1.6) 就不再需要。这是我对 BLR 草图的阅读，BLR 没有写成定理，我也没有写出完整证明。**(b)** 非阿基米德同型结果：Fan–Fan–Ye 引理 6.3（arXiv:2512.05690v1）对缩放比为 $q^{\lambda_n}$ 的 scaling map，只假设 $\lambda_1\ge H_0$ 与 $\lambda_{n+1}-\lambda_n\ge H_n$（相当于 BLR 的 (1.5)），**不假设 (1.6)**，证明 $\dim_H\Gamma_{b,H}=\liminf_n\frac{\lambda_n-\sum_{k<n}H_k}{\lambda_n+H_n}$，形式正是 BLR 公式。scaling map 没有失真，恰好对应实数情形的线性映射。**(c)** 下层工具是齐次 Moran 集的维数公式（FWW 1997，论文已引） | BLR v1 草图逐字；arXiv:2512.05690v1 引理 6.3（TeX 源与 arXiv HTML 编号均已核） |

**含义**：2B 的维数相变在方法上是"BLR / Moran 论证在线性情形下的落实"。它能写成一个干净的定理，但不会被视为新方法。论文第 2488 行附近与 `rem:growing-BLR` 中"extension of that formula beyond condition (1.6)"的说法可以保留，但建议补一句：线性情形下 (1.6) 只用于吸收失真，失真并不存在。同时引用 Fan–Fan–Ye 引理 6.3 作为非阿基米德的同型结果。是否修改由作者决定。

---

## 3. 非线性情形：负搜索未找到先例（真正的研究问题）

- **问题陈述**：对非线性 $f_n$（典型例子是 $f_n(x)=x^n$），当 $\log f'_{n+1}/\log f'_n\to1$ 时，求 $\{x:\lVert f_n(x)-y_n\rVert\le\delta_n\ \forall n\}$ 在 $\delta_n\to0$ 或 $\delta_n$ 为常数时的精确（局部）Hausdorff 维数。
- **已知的相邻结果**（全部经 Fan–Fan–Ye 引言**转引**，原文未核到）：
  - Pollington 1980：$\{x>1:\{x^n\}<\epsilon\ \forall n\}$ 满维数；
  - Kahane 2014：$\dim\{x>1:\lVert x^n-b_n\rVert<\epsilon\ \forall n\}=1$；
  - Baker 2015：若 $r_{n+1}-r_n\to\infty$，则 $\dim\{x>1:\lVert x^{r_n}-b_n\rVert\to0\}=1$。

  这些都是**整体满维数**的结论，不是给定 $\delta_n$ 下的精确局部公式。
- **为什么难**（本核查的分析，未证明）：
  - 失真误差 $\sum_{j<n}\log(f_j'(z_j)/f_j'(z))$ 在 $\log f_n'$ 只线性增长时不能被忽略；
  - 当每层分支数 $m_n\approx2\delta_{n-1}f_n'/f_{n-1}'$ 保持有界时（例如 $x^n$、$\delta$ 为常数，$m\approx2\delta v$），维数取决于精确的整数计数，"$\pm2$"误差不能被吸收，BLR 型渐近公式本身可能不再精确。
- **对论文二的意义**：这已经**不是**论文二的内容（论文二只用线性映射 $Q_jx$），而是"实数幂次模 1 的分布"方向上的独立问题。如果做出"给定 $\delta_n$ 下 $\{x:\lVert x^n-y_n\rVert\le\delta_n\ \forall n\}$ 的精确局部维数"，可见度会远高于 $e$ 收敛分母上的谱结果。但它的可行性与难度**未评估**；本节关于先例的结论只是负搜索。

---

## 4. 检索式（arXiv API，`abs:` 字段，2026-11-24 执行）
1. "fractional parts" AND "Hausdorff dimension" AND "for all"（命中 2 条，无关）
2. "distribution modulo one" AND "Hausdorff dimension" AND "exceptional"（2 条，无关）
3. "powers of real numbers" AND "Hausdorff dimension"（0 条）
4. lacunary AND "Hausdorff dimension" AND "tends to zero"（0 条）
5. "shrinking target" AND "Hausdorff dimension" AND "all n"（1 条，无关）
6. Moran AND "fractional parts" AND dimension（0 条）
7. "badly distributed" AND dimension（2 条，无关）

**WebSearch**：
- （扩展）Hausdorff dimension set of x with ‖a_n x − y_n‖ ≤ δ_n for all n lacunary sequence formula liminf
- Hausdorff dimension {x>1 : ‖x^n − y_n‖ ≤ δ_n for all n} … Bugeaud Liao Rams Theorem 7 generalization

两次都没有找到所需公式；返回的最接近结果是 BLR 本身、Liao–Rams 的非齐次逼近，以及"对充分大的 $n$ 成立"型 liminf 集的相关讨论。

## 5. 它没做到什么
- 没有写出线性情形"(1.6) 可换成 $n=o(\log a_n)$"的完整证明；这是对草图的阅读。
- 没有查 zbMATH / MathSciNet 引用链；OpenAlex 与 Semantic Scholar 的引用列表可能不全。
- 没有评估非线性情形的可行性。
