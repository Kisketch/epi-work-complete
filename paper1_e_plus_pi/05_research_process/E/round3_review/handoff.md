# 配套论文文献对照

依据当前配套稿的定理标签与源文进行核查。下列判断限于列出的原始来源。

| 本稿命题 | 原始来源 | 假设匹配 | 可引用范围 |
|---|---|---|---|
| 无权零极限的维数 1 | Bugeaud–Liao–Rams, Cor. 8，作者稿 p. 5 | 取 a_j=Q_j，目标中心为 0。分母递推给 Q_{j+1}/Q_j→∞ | 直接特例。推广到全实数是定理已给的范围 |
| 定理 11 的规定极限 | Bugeaud–Liao–Rams, Thm. 7、(1.5)–(1.7)，作者稿 p. 5 | f_j(x)=Q_j x 时导数无畸变，移动目标可取 c j^{-α}，优选误差窗 δ_j=j^{-α}/log(j+2)。0<α<1 时 (1.5) 在删有限首项后成立。论文仍需 (1.6) 的导数对数比趋于 ∞；这里 log Q_{j+1}/log Q_j→1 | 相关构造，无法直接推出规定极限的正权重结果。定理结论处理所有层上的缩小窗及局部维数 |
| 定理 11 的下界 | Feng–Wen–Wu, Thm. 2.1，印刷 p. 478 | 剪枝保留同层相同子代数和相同区间长度。Moran 收缩比为相邻长度之比，满足兄弟区间内部互斥。下界分母中的末层因子仅造成 O(log j) 的修正 | 剪枝后构造得到的下界是直接应用。全文须另给规定极限全集的覆盖上界 |
| 定理 12 的临界标度 | Cabrelli–Mendivil–Molter–Shonkwiler, Thm. 3，印刷 p. 57 | 来源从非增的正间隙序列 a、总长 1 出发，为其特定 Cantor 集 C_a 构造匹配 h，证明 H^h(C_a) 有限且为正。此处先由 Hermite Q_j 固定 h_k，再研究整个 Λ=k/4 集合 | 相关的广义 Hausdorff 测度方法。全文的严格子水平集零测度、整个精确层 σ 有限及无穷都由本稿的额外论证给出。未核得可直接推出这些结论的对应项 |
| 定理 14 的维数对照 | Chousionis–Leykekhman–Urbański, Prop. 2.7、Thm. 4.9 证明中的 (4.8)，作者稿 pp. 8–9、23 | (4.8) 用固定字母表 E_{s,q}，取 s=1,q=4 即得 F 的 0.744 上界；比较 E_{1,3} 与 E_{1,4} 时按序配对逐项非减，满足其压力比较证明实际使用的条件 | 0.744 可借本稿 E、F 等维得到 E 的上界。本稿允许按位置改变余数，这是与固定字母表框架的准确区别。5/7 比此处所引上界更紧，归于本稿分支导数估计 |

BLR 源文 Thm. 7 条件 (1.6) 的右端为 ∞，作者修订稿和 arXiv 版本一致。CLU Prop. 2.7 印行稿对照暂未取得，作者稿陈述只写 increasing bijection，但证明明确用 s(a)≥a；(4.8) 的当前引法满足这一条件。

## 可写入英文表述

- “Bugeaud, Liao and Rams' Corollary 8 applies to the unweighted zero-limit set since Q_{j+1}/Q_j tends to infinity. Our weighted prescribed-limit theorem uses the elementary construction below because the logarithmic growth condition (1.6) of their Theorem 7 fails for f_j(x)=Q_j x.”
- “After retaining a common number of children in every interval of a given level, Feng, Wen and Wu's Theorem 2.1 also yields the lower bound. The covering argument treats the full prescribed-limit set.”
- “Cabrelli, Mendivil, Molter and Shonkwiler's Theorem 3 gives a positive and finite generalized Hausdorff measure for their gap-generated Cantor set with a gauge obtained from its gap sequence. Here the recurrence fixes the gauge, and the covering and translation arguments determine the measure class of the whole critical level.”
- “For the fixed alphabet E_{1,4}, equation (4.8) of Chousionis, Leykekhman and Urbański gives a dimension bound of 0.744. The position-dependent digit comparison transfers that bound to the eventual-periodicity set. The sharper bound 5/7 follows from the branch estimates above.”

## 原始来源

- Y. Bugeaud, L. Liao and M. Rams, *Metrical results on the distribution of fractional parts of powers of real numbers*, Proc. Edinburgh Math. Soc. **62** (2019), 505–521. [刊版记录](https://doi.org/10.1017/S0013091518000585) · [作者修订稿](https://irma.math.unistra.fr/~bugeaud/travaux/power-diop-revised.pdf)
- D. Feng, Z. Wen and J. Wu, *Some dimensional results for homogeneous Moran sets*, Sci. China Ser. A **40** (1997), 475–482. [作者馆藏](https://www.math.cuhk.edu.hk/~djfeng/fengpapers/old-papers/FWW_SC.pdf)
- C. Cabrelli, F. Mendivil, U. M. Molter and R. Shonkwiler, *On the Hausdorff h-measure of Cantor sets*, Pacific J. Math. **217** (2004), 45–59. [刊版全文](https://msp.org/pjm/2004/217-1/pjm-v217-n1-p04-p.pdf)
- V. Chousionis, D. Leykekhman and M. Urbański, *On the dimension spectrum of infinite subsystems of continued fractions*, Trans. Amer. Math. Soc. **373** (2020), 1009–1042. [作者书目](https://www2.math.uconn.edu/~chousionis/publications.html) · [arXiv:1805.11904](https://arxiv.org/pdf/1805.11904)

## 谱隙的精确归属补充

令 α=(e+1)/2。利用主稿的递推，取 R_j=(P_j+Q_j)/2；(R_0,Q_0)=(1,1)，(R_1,Q_1)=(2,1)。从 j=1 开始的系数为 4j+2，所以 R_j/Q_j 正是 [1;1,6,10,14,...] 的完整收敛分数序列；极限由 P_j/Q_j→e 得到。Biró–Deshouillers–Sós 印刷 p.106 转述的 Kraaikamp–Liardet 引理给出 x∉Z+Zα 时，||Q_jx||>(1/4)Q_j|Q_jα−R_j| 对无穷多 j 成立。由普通收敛分数误差公式，Q_j|Q_jα−R_j|=(4j+2+O(1))^{-1}。故在本设定中，既有文献已推出 1/16 的弱间隙，并结合格点的直接估计得到零层分类。配套稿的 1/4 gap 把这一引理给出的定量常数提高为锐常数。

建议英文：“Although Q_j is a subsequence of convergent denominators of e, it is the full convergent-denominator sequence of α=(e+1)/2=[1;1,6,10,14,…], with the initial denominator 1 repeated. The Kraaikamp–Liardet estimate, as quoted by Biró, Deshouillers and Sós (p. 106), therefore recovers the zero-level lattice and yields the lower bound 1/16 outside it. The gap argument below gives the sharp value 1/4 for this recurrence.”

Biró, Deshouillers and Sós, *Good approximation and characterization of subgroups of R/Z*, Studia Sci. Math. Hungar. **38** (2001), 97–113. The lemma on p. 106 is the one quoting Kraaikamp and Liardet. [Rényi 院馆藏和原文](https://real.mtak.hu/110616/)

## 主稿窗口定理的相关文献

Stambul, *A generalization of Perron's theorem about Hurwitzian numbers*, Acta Arith. **80** (1997), 141–148, p. 141 引述 Perron pp. 127–131 的整系数 Möbius 不变性，并另引非恒定准周期多项式次数不变。因此有理平移的 Hurwitzian 性、由此得到的多项式次数属于已有成果；论文的主张应聚焦 Hermite 截止位置、显式阈值、窗口周期 2B² 和首商平方增量。Stambul p. 143 还陈述用换能器处理更广的常系数线性递推数字类。该陈述未提供上述窗口的具体尺度。未核到 Perron 原书页内的同等定量界，因此范围以已查 Stambul 为限。[刊页](https://doi.org/10.4064/aa-80-2-141-148) · [原文](https://matwbn.icm.edu.pl/ksiazki/aa/aa80/aa8023.pdf)
