# P4 与二次 Lagrange 谱先例全文核查记录

> **一句总判断**：已完成 7 篇核心先例文献的全文与 CrossRef 元数据核对，确认：(1) 在二次 Lagrange 谱方向，Lin (2018) Lemma 4.2 处理的是 $\liminf a_r = \infty$ 情形（$c_\varphi(\xi)=3/\sqrt{5}-1=K_\varphi$），与论文一 §8 的 $(A_k,1,1)$ 区间（$\liminf a_r = 1$，$c_\varphi(x)=1-2/\sqrt{5}$ 及第二极限点 $4/\sqrt{5}-1$）无重叠；(2) 在 Hurwitz 连分数仿射窗口方向，Matthews & Walters (1970) Theorem 1(b) 已对齐次情形 $A=0$（$(m/n)e$）给出显式周期与平方 gcd 增量，因此论文一 `thm:affine-window` / `cor:affine-single` 的推进边界必须收紧至**非齐次仿射平移 $A\ne 0$、Hermite 截断窗口长度 $r_j$ 与 5-窗锐性刻画**；2018–2026 年区间为**负搜索未找到先例**，不宣称已证明不存在先例。

---

## 0. 诚实分类总表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| Parkkonen & Paulin (2011) + Erratum (2014) 全文/DOI 核对 | 5. 文献核查与复现 | 已核实（CrossRef + 全文） | 确立二次 Lagrange 谱（双曲几何/离散子群框架）基础 | *Math. Z.* 268 (2011), no. 1–2, 101–142 (`doi:10.1007/s00209-010-0662-0`)；Erratum: *Math. Z.* 276 (2014), 1215–1216 (`doi:10.1007/s00209-013-1239-5`) |
| Bugeaud (2014) 全文/DOI 核对 | 5. 文献核查与复现 | 已核实（CrossRef + 全文） | 给出连分数版二次 Lagrange 谱、式 (3.4) 及 $c_\varphi(x)=0$ 判据；未计算 $c_\varphi(e)$ 或 $(A_k,1,1)$ 精确值 | *Math. Z.* 276 (2014), no. 3–4, 985–999 (`doi:10.1007/s00209-013-1230-1`) |
| Pejković (2016) 全文/DOI 核对 | 5. 文献核查与复现 | 已核实（CrossRef + 全文；修正旧无效 DOI） | 改进二次 Lagrange 谱极大值与孤立点结果；未处理 $(A_k,1,1)$ 型 Hurwitz 数的 $c_\varphi(x)$ 与第二极限点 | *Math. Z.* 283 (2016), no. 3–4, 861–869 (`doi:10.1007/s00209-016-1624-y`)；预印本页码标明 `preprint p. 2 / p. 4` |
| Lin (2018) 全文/DOI 核对（含 Lemma 4.2） | 5. 文献核查与复现 | 已核实（CrossRef + arXiv 全文） | Lemma 4.2（`arXiv:1703.04847v2`, p. 14）对 $\liminf a_r=\infty$ 证得 $c_\varphi(\xi)=\frac{3}{\sqrt{5}}-1=K_\varphi$，与论文一 §8 的 $\liminf a_r=1$ 情形无重叠 | *Math. Z.* 289 (2018), no. 1–2, 515–533 (`doi:10.1007/s00209-017-1964-2`)，`arXiv:1703.04847v2` |
| Stambul (1997) 全文/DOI 核对 | 5. 文献核查与复现 | 已核实（CrossRef + 全文） | 推广 Perron 关于 Hurwitzian 数的经典定性定理（一般 Möbius 变换保持 Hurwitzian 性） | *Acta Arith.* 80 (1997), no. 2, 141–148 (`doi:10.4064/aa-80-2-141-148`) |
| Hetyei (2014) 全文/DOI 核对 | 5. 文献核查与复现 | 已核实（CrossRef + 全文） | 二次/组合视角下的 Hurwitzian 连分数；修正论文一原书目题名截断、缺页码/DOI 及正文零引用问题 | *SIAM J. Discrete Math.* 28 (2014), no. 2, 962–985 (`doi:10.1137/130926092`) |
| Matthews & Walters (1970) 全文/DOI 核对（Theorem 1(b)） | 5. 文献核查与复现 | 已核实（CrossRef + 全文） | Theorem 1(b) 已对齐次情形 $A=0$（$(m/n)e$）给出显式周期 $d=mn$、显式起点及平方 gcd 增量 $p_t^2(2x-1)$（每 $2mn$ 步增 $4p_t^2$）；据此收紧 `thm:affine-window` / `cor:affine-single` 边界 | *Math. Proc. Cambridge Philos. Soc.* 67 (1970), no. 1, 67–74 (`doi:10.1017/S0305004100057108`) |
| 2018–2026 年二次 Lagrange 谱后续文献检索 | 5. 文献核查与复现（负搜索） | 负搜索未找到先例 | 检索范围涵盖 CrossRef / arXiv / MathSciNet 公开索引中“quadratic Lagrange spectrum”与“Hurwitz continued fraction”相关条目，未见 $(A_k,1,1)$ 精确 $c_\varphi(x)$ 与第二极限点定理 | 负搜索记录（**不宣称已证明不存在先例**） |

**它没做到什么（边界声明）**：
- 对 2018–2026 年间非公开、非英文或未收录于上述检索词的文献无法穷尽，因此严格限定为「**负搜索未找到先例**」，不宣称「已证明不存在先例」。
- 本文献核查仅收紧论文一 §8 辅助结果的新颖性口径，**不改变 $e+\pi$ 无理性仍为公开问题的事实**。

---

## 1. 二次 Lagrange 谱方向（方向 2）核查细目

1. **Parkkonen & Paulin (2011) 及 Erratum (2014)**：
   - 书目：J.~Parkkonen and F.~Paulin, *Spiraling spectra of geodesic lines in negatively curved manifolds*, Math.~Z.~268 (2011), no.~1--2, 101--142, `doi:10.1007/s00209-010-0662-0`；Erratum: Math.~Z.~276 (2014), no.~3--4, 1215--1216, `doi:10.1007/s00209-013-1239-5`。
   - 核查结论：给出二次无理数轨道逼近谱的一般几何框架与极大值估计，未对 $(A_k,1,1)$ 型无理数给出 $c_\varphi(x)=1-2/\sqrt{5}$ 或第二极限点 $4/\sqrt{5}-1$。
2. **Bugeaud (2014)**：
   - 书目：Y.~Bugeaud, *On the quadratic Lagrange spectrum*, Math.~Z.~276 (2014), no.~3--4, 985--999, `doi:10.1007/s00209-013-1230-1`。
   - 核查结论：全文核对确认式 (3.4)（Möbius 误差恒等式）与 Lemma 2.1--2.2、Corollary 2.3、Lemma 4.1（$c_\varphi(x)=0 \iff$ 任意长连续 $1$ 块）；未计算 $c_\varphi(e)$ 或 $(A_k,1,1)$ 族。
3. **Pejković (2016)**：
   - 书目：T.~Pejković, *Quadratic Lagrange spectrum*, Math.~Z.~283 (2016), no.~3--4, 861--869, `doi:10.1007/s00209-016-1624-y`（修正了此前草稿中的无效 DOI；引用预印本定位时标明 `preprint p. 2 / p. 4`）。
   - 核查结论：改进二次 Lagrange 谱极大值与孤立点，未涉及 $(A_k,1,1)$ 型 Hurwitz 数的精确值与第二极限点。
4. **Lin (2018)**：
   - 书目：X.~Lin, *Quadratic Lagrange spectrum: I*, Math.~Z.~289 (2018), no.~1--2, 515--533, `doi:10.1007/s00209-017-1964-2`（`arXiv:1703.04847v2`）。
   - 核查结论：Lemma 4.2（`arXiv:1703.04847v2`, p.~14）证明当 $\liminf_{r\to\infty} a_r = \infty$ 时，$c_\varphi(\xi) = \frac{3}{\sqrt{5}} - 1 = K_\varphi$。论文一 §8 定理 `thm:golden-exact-second` 处理的是最终形如 $(A_k,1,1)$（$A_k\to\infty$）的连分数，其 $\liminf_{r\to\infty} a_r = 1$，所得精确值 $c_\varphi(x) = 1 - \frac{2}{\sqrt{5}}$ 与第二最小极限点 $\frac{4}{\sqrt{5}} - 1$ 均位于 Lin (2018) Lemma 4.2 覆盖区间之外，两者无重叠。

---

## 2. Perron / Stambul / Matthews–Walters 边界核查细目（方向 3-P4）

1. **Stambul (1997)**：
   - 书目：P.~Stambul, *A generalization of Perron's theorem about Hurwitzian numbers*, Acta Arith.~80 (1997), no.~2, 141--148, `doi:10.4064/aa-80-2-141-148`。
   - 边界：推广 Perron 定理，定性刻画 Hurwitzian 数在有理分式线性变换下的封闭性；不提供 Hermite 截断窗口长度 $r_j$ 的显式周期与单字窗口 5-窗锐性刻画。
2. **Hetyei (2014)**：
   - 书目：G.~Hetyei, *Hurwitzian continued fractions containing a repeated constant and an arithmetic progression*, SIAM J.~Discrete Math.~28 (2014), no.~2, 962--985, `doi:10.1137/130926092`（`arXiv:1211.2494`）。
   - 边界：原论文一 `\bibitem{Hetyei2014}` 题名截断为 *Hurwitzian continued fractions* 且缺期号、页码、DOI、正文零引用；现已补全完整书目并在 §8 恰当引用。
3. **Matthews & Walters (1970)**：
   - 书目：K.~R.~Matthews and R.~F.~C.~Walters, *Some properties of the continued fraction expansion of $(m/n)e^{1/q}$*, Math.~Proc.~Cambridge Philos.~Soc.~67 (1970), no.~1, 67--74, `doi:10.1017/S0305004100057108`。
   - **关键边界收紧**：Matthews & Walters (1970) Theorem 1(b) 已对齐次情形 $A=0$（即 $(m/n)e$）给出了显式周期 $d=mn$、显式起点以及平方 gcd 增量 $p_t^2(2x-1)$（每 $2mn$ 步增量为 $4p_t^2$）。因此，论文一 `thm:affine-window` 与 `cor:affine-single` **不能**宣称对 $A=0$ 的 $(C/B)e$ 首次给出显式周期或平方 gcd 增量；其确切推进边界应表述为：
     1. 统一覆盖**非齐次仿射平移 $A\ne 0$** 的 $x=(A+Ce)/B$（尤其 $A/B-e$）；
     2. 结合 Hermite 选定渐近分数截断给出**窗口长度 $r_j$ 的显式周期与 $r_j=1 \iff G_j G_{j+1}=T$ 判据**；
     3. 证明连续单字窗口的 **5-窗锐性刻画**（`cor:affine-single`，反例 $x=(1+e)/6$ 给出 4 窗极限）。
