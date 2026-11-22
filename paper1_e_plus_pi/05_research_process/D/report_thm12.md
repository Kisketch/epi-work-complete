# D 组判定二：第二阶段定理 12（thm:gauge）审稿结论

**结论：定理 12 的数学论证成立，未发现反例或失效公式。三个被点名环节均能通过独立复核，
但正文有若干隐含步骤未写明（可测性、σ-有限分支、端点与极小直径覆盖的口径）。
判定为「纸面证明成立、建议按下文补写」，不是机器验证（定理 12 本身无 Lean 形式化）。**

审稿对象：`第二阶段修订/Phase2_revised.tex` 第 303–362 行（§A Hausdorff gauge at the critical weight）。
定理陈述：对整数 k≥1，b=2k+1，gauge h_k 满足 h_k(1/Q_n)=b^{−n}（线性插值），则圆周上
精确水平集 {Λ=k/4} 的 H^{h_k} 测度无穷但 σ-有限；严格次水平集 {Λ<k/4} 的 H^{h_k} 测度为零。

## 环节一：短区间能对应几个不同的缺陷前缀

正文（第 341–346 行）：长度 h 满足 1/Q_{n+1}≤h<1/Q_n 的区间，在每个 N≤j<n 至多决定一个 M_j，
在水平 n 至多三个选择；这些整数恢复至 n−1 的全部数字，故区间质量 ≤3b^{−(n−N)}。

**独立复核（通过）：**
- 同一短区间内两点 x,y：|Q_j(x−y)| ≤ Q_j·h < Q_j/Q_n ≤ 1/4（j<n，用 Q_{j+1}≥4Q_j，
  共享库 `Qsel_double_all` 给系数≥6，更强）。两个最近整数之差 <1/4+1/4=1/2<1，故 M_j 唯一。
  正文写「differ by less than 1/4+Q_j/Q_n<1」，常数略松但方向正确，结论不受影响。
- 水平 n 的「至多三个」：区间长 h<1/Q_n，而水平 n 中心间距 1/Q_n，长度小于间距的区间
  至多碰 3 个网格中心（含两端各一个部分重叠）。这是标准的网格计数，成立。
- 数字恢复：d_j=M_{j+1}−A_jM_j−M_{j−1}（A_j=4j+2）。给定 M_{N−1},M_N 与 d_N,…,d_{n−1}
  可递推恢复 M_{n}；反之给定 M_{N−1},…,M_n 可恢复 d_N,…,d_{n−1}。故「至多 3 个 M_n 选择」
  对应「至多 3b^{n−N} 条数字路径」，每条质量 b^{−(n−N)}，合计 ≤3b^{−(n−N)}。成立。
- 质量分布原理（mass distribution principle）：区间质量 ≤3b^{N+1}·h_k(h) 对一切短区间成立
  ⇒ H^{h_k}(紧数字像) ≥ 1/(3b^{N+1}) > 0。成立。

**边界/口径问题（非致命，需补写）：**
- 端点：M_j=round(Q_jx) 在半整数处有歧义。但歧义集是 {x:Q_jx∈ℤ+1/2} 的可数并，
  对任何非原子测度为零；且数字构造中 |u_j|<1/8 远离半整数，构造点不受影响。
  正文未提，建议加一句「舍入歧义集可数，不影响测度与构造」。
- 「至多三个」在 h 恰好 =1/Q_{n+1} 或区间跨原点时需按圆周口径数；正文末尾已说
  「construction in a real interval also works on the circle by splitting across the origin」，
  覆盖了跨原点情形。可接受。

## 环节二：从整个次水平集到精确水平集为何仍有正测度

正文（第 339、349–350 行）：数字构造的紧像落在次水平集 {Λ≤k/4}；
「Removing the null strict sublevel preserves positivity」。

**独立复核（通过，但有一个必须写明的包含关系）：**
- 上界方向：Λ(x)≤k/4 ⇒ 最终 |u_j|≤(k+1)/j ⇒ limsup|d_j|≤k ⇒ 最终 |d_j|≤k（整数）。
  严格方向：Λ(x)<k/4 ⇒ 最终 |d_j|≤k−1。这两条用 d_j=A_ju_j+u_{j−1}−u_{j+1} 与
  A_j/j→4 直接得出，成立。
- 构造方向：任取数字 d_j∈{−k,…,k}，递推 M_{j+1}=A_jM_j+M_{j−1}+d_j，
  W_j=M_{j+1}Q_j−M_jQ_{j+1} 满足 W_j=d_jQ_j−W_{j−1}，|W_j|≤2kQ_j（分母至少倍增），
  望远镜得 |x−M_j/Q_j|≤4k/Q_{j+1}。取 N 大使 |u_j|<1/8，则 M_j 确为最近整数，
  且 |4ju_j−d_j|≤2|u_j|+|u_{j−1}|+|u_{j+1}|→0，故 limsup j|u_j|=limsup|d_j|/4≤k/4。
  **关键包含：数字像 ⊆ {Λ≤k/4}（次水平集），不一定落在精确水平集 {Λ=k/4}。**
- 正测度传递：H^{h_k}(数字像)>0（环节一），而 {Λ<k/4}（严格次水平集）的 H^{h_k} 测度为零
  （正文用 2k−1<b 的覆盖成本趋于零证明）。于是
  H^{h_k}({Λ=k/4}) ≥ H^{h_k}(数字像 ∩ {Λ=k/4}) = H^{h_k}(数字像) − H^{h_k}(数字像 ∩ {Λ<k/4}) > 0。
  **这一步成立的前提是「严格次水平集 H^{h_k}-零」已独立证明**——正文第 325–327 行确实用
  「count uses 2k−1<b」给了覆盖论证。逻辑闭合。

**必须补写的点：**
- 正文「The compact image of the digit space lies in the sublevel」用的是**非严格**次水平集
  {Λ≤k/4}，而「Removing the null strict sublevel」移除的是**严格**次水平集 {Λ<k/4}。
  两者不同，正是精确水平集 {Λ=k/4} 非空的来源。建议把这两个集合的符号显式区分，
  避免读者误以为数字像直接落在精确水平集上（那需要额外证明 limsup 恰等于 k/4，正文没证也不需要）。
- 「严格次水平集 H^{h_k}-零」的覆盖论证（2k−1<b）应明确写成独立引理，因为环节二的正测度
  传递完全依赖它。当前它混在定理 12 证明第一段，建议单列。

## 环节三：稠密子群平移不变性 ⇒ 有限归一化测度 = 圆周 Lebesgue

正文（第 352–361 行）：精确水平集是 Lebesgue 零的 Borel 集，在模 1 加 L 下不变；
L 稠密（(e+1)/2 无理）。若其 H^{h_k} 测度有限且正，限制并归一化得概率测度，
在稠密子群下不变 ⇒ 在整个圆周下不变 ⇒ 归一化 Lebesgue ⇒ 不能支撑在零水平集上 ⇒ 矛盾 ⇒ 测度无穷。

**独立复核（通过，σ-有限分支需补写）：**
- 不变性：y∈L ⇒ j‖Q_jy‖→0（分类定理，机器验证 `Classification.theorem2_classification`）。
  于是 Λ(x+y)=Λ(x)（limsup 加一个趋于 0 的量不变），精确水平集在 +L 下不变。成立。
  **注意**：这里用到的是「j‖Q_jy‖→0」而非仅「‖Q_jy‖→0」，权重 j 不可省；分类定理恰给前者。
- 稠密性：L=ℤ+ℤ(e+1)/2，(e+1)/2 无理（e 无理 ⇒ (e+1)/2 无理），故 L 模 1 稠密。成立。
  e 无理在共享库是 `e_irrational`（依赖公理 e_transcendental，属 T3 公理化经典事实）。
- 稠密不变 ⇒ 全不变：对连续函数 f，∫f dμ 在稠密子群平移下不变，由连续性延拓到全圆周。
  圆周上平移不变概率测度唯一 = 归一化 Lebesgue（用长度 1/m 的弧质量 1/m，有理弧决定测度）。
  这是标准论证，成立。
- 矛盾：归一化 Lebesgue 不能支撑在 Lebesgue 零集上。精确水平集 Lebesgue 零由
  定理 thm:finite（dimH E_c=0，机器验证 `DimHFinite.dimH_levelSet_finite`，仅基础公理）给出。成立。

**σ-有限与可测性（必须补写，当前正文未交代）：**
- **可测性**：精确水平集 {Λ=k/4} 须是 Borel 才可谈 H^{h_k} 限制与归一化。
  Λ=limsup j‖Q_jx‖，x↦j‖Q_jx‖ 连续（distToNearestInt 连续），limsup 的可测性给出
  {Λ≤c} 为 Borel（可数交并），故 {Λ=k/4}={Λ≤k/4}∩{Λ≥k/4} Borel。
  正文第 352 行直接说「the exact level is a Borel set」但未给理由，建议补一句上述推导。
  共享库 `SpectralGap.levelSet` 定义了 {Λ≤c}，但未证 MeasurableSet；这是形式化缺口（若将来要形式化）。
- **σ-有限分支**：定理结论是「无穷但 σ-有限」。正文反证只处理了「有限且正」⇒矛盾⇒无穷。
  但「无穷」之后还需证 σ-有限，正文未写。实际上 σ-有限来自覆盖：精确水平集 ⊆ E_{k/4}（有限水平集），
  而 E_{k/4} 被可数个 Cantor 类 C_J 覆盖，每类 H^{h_k} 有限（正文第 322–326 行「finite covering cost per class」）。
  故精确水平集 σ-有限。**建议把「σ-有限」的证明显式补上**，当前它是结论里声称但证明里缺失的一半。
- **极小直径覆盖**：gauge h_k 只在 1/Q_n 处定值、其间线性插值，「only its values near zero matter」。
  Hausdorff 测度用直径→0 的覆盖，h_k 在 (1/Q_{n+1},1/Q_n) 的线性插值保证单调连续，
  覆盖成本 h_k(diam U) 对极小直径有定义。正文未讨论 h_k 是否单调/连续到 0，
  但「increasing continuous gauge, h_k(0)=0」已声明，足够。可接受。

## 综合判定

| 环节 | 判定 | 说明 |
|------|------|------|
| 一：短区间 ↔ 缺陷前缀 | ✅ 成立 | 常数 1/4+Q_j/Q_n 略松但方向对；端点歧义集可数，需补一句 |
| 二：次水平集 → 精确水平集正测度 | ✅ 成立 | 依赖「严格次水平集 H^{h_k}-零」独立引理；需显式区分 {Λ≤k/4} 与 {Λ<k/4} |
| 三：稠密平移不变 ⇒ Lebesgue ⇒ 无穷 | ✅ 成立 | 需补 Borel 可测性推导与 σ-有限分支 |

**未发现反例或失效公式。** 三个环节的核心数学都站得住。问题全部是「正文未写明的隐含步骤」，
属可补写的表述缺口，不是逻辑错误。定理 12 维持「纸面证明」层，**不能**标为机器验证
（它本身没有 Lean 形式化；其依赖的分类定理、有限水平集维数定理已机器验证，但 gauge 构造、
质量分布、稠密不变性论证均未形式化）。

## 可替换进正文的修正段落

以下英文段落可直接替换/插入 Phase2_revised.tex 定理 12 证明，补齐三处隐含步骤：

```latex
\begin{proof}[Proof of Theorem~\ref{thm:gauge}, revised]
Write $A_j=4j+2$, let $M_j$ be a nearest integer to $Q_jx$, put
$u_j=Q_jx-M_j$, and define $d_j=M_{j+1}-A_jM_j-M_{j-1}$, so
$d_j=A_ju_j+u_{j-1}-u_{j+1}$. The rounding ambiguity occurs only on the
countable set $\bigcup_j\{x:Q_jx\in\Z+\tfrac12\}$, which is null for every
non-atomic measure and is avoided by the construction below.

If $\Lam(x)\le k/4$, eventually $|u_j|\le(k+1)/j$ and $\limsup|d_j|\le k$,
so the integer digits eventually satisfy $|d_j|\le k$. For the \emph{strict}
sublevel $\Lam(x)<k/4$ this improves to $|d_j|\le k-1$. Partition into
countably many Borel classes by a common starting index $N$ and the two
starting integers, requiring the stated inequalities at all indices past $N$.
By level $n$ there are at most $b^{\,n-N}$ possible $M_n$ per class, each
giving an interval of diameter $\le2(k+1)/(nQ_n)\le1/Q_n$ eventually; this
gives a finite covering cost per class. For the strict sublevel the count
uses $2k-1<b$, so its covering cost tends to zero:
\begin{equation}\label{eq:strict-null}
 \mathcal H^{h_k}\bigl(\{x:\Lam(x)<k/4\}\bigr)=0 .
\end{equation}

For positivity fix a large $N$, set $M_{N-1}=M_N=0$, and prescribe arbitrary
digits $d_j\in\{-k,\ldots,k\}$ for $j\ge N$. With
$W_j=M_{j+1}Q_j-M_jQ_{j+1}$ one has $W_j=d_jQ_j-W_{j-1}$, $W_{N-1}=0$, and
$|W_j|\le2kQ_j$ since the denominators at least double; telescoping gives a
limit $x=\lim M_j/Q_j$ with $|x-M_j/Q_j|\le4k/Q_{j+1}$. Choose $N$ so that
$|u_j|<1/8$ for all $j\ge N$; then $M_j$ is indeed nearest and
$|4ju_j-d_j|\le2|u_j|+|u_{j-1}|+|u_{j+1}|\to0$. Hence the compact digit image
$K$ satisfies $K\subseteq\{x:\Lam(x)\le k/4\}$ (the \emph{non-strict}
sublevel). Give the digits equal independent weights. An interval of length
$1/Q_{n+1}\le h<1/Q_n$ determines at most one $M_j$ at each $N\le j<n$ (two
points in it have nearest integers differing by $<1/4+Q_j/Q_n<1$) and at most
three choices at level $n$; these recover all digits through $n-1$, so its
mass is $\le3b^{-(n-N)}\le3b^{N+1}h_k(h)$. The mass distribution principle
gives $\mathcal H^{h_k}(K)>0$. Since $K\subseteq\{\Lam\le k/4\}$ and
\eqref{eq:strict-null} removes only the strict part,
\[
 \mathcal H^{h_k}\bigl(\{x:\Lam(x)=k/4\}\bigr)
 \ \ge\ \mathcal H^{h_k}(K)-\mathcal H^{h_k}\bigl(\{\Lam<k/4\}\bigr)
 \ =\ \mathcal H^{h_k}(K)\ >\ 0 .
\]

Finally $\{x:\Lam(x)=k/4\}$ is Borel: $x\mapsto j\|Q_jx\|$ is continuous and
$\Lam$ is a limsup of these, so $\{\Lam\le c\}$ is Borel for every $c$, and
$\{\Lam=k/4\}=\{\Lam\le k/4\}\cap\{\Lam\ge k/4\}$. It has Lebesgue measure
zero by Theorem~\ref{thm:finite}. It is invariant under addition of $L$
modulo one, since $j\|Q_jy\|\to0$ for $y\in L$; this subgroup is dense as
$(e+1)/2$ is irrational. If its $\mathcal H^{h_k}$ measure were finite and
positive, restricting and normalizing would give a probability invariant
under this dense subgroup; integrating continuous functions and taking limits
gives invariance under the entire circle, hence normalized Lebesgue measure,
which cannot be supported on a Lebesgue-null set. Thus the measure is
infinite. It is $\sigma$-finite because $\{\Lam=k/4\}\subseteq E_{k/4}$ and
$E_{k/4}$ is covered by the countably many classes above, each of finite
$\mathcal H^{h_k}$ cost.
\end{proof}
```

## 给总控的形式化缺口清单（若将来要把定理 12 机器化）

1. `MeasurableSet (levelSet c)`：limsup 连续函数列的可测性（mathlib 有
   `measurable_limsup`，需接 `Continuous.measurable`）。
2. 严格次水平集 H^{h_k}-零（2k−1<b 覆盖）独立引理。
3. 数字像紧性 + 质量分布原理（mathlib `MeasureTheory.Measure.hausdorffMeasure` 相关）。
4. 稠密子群不变概率 = Lebesgue（圆周 Haar 唯一性）。
5. σ-有限分支。
以上均非本轮范围（首轮只核验命题 8.1 + 纸面审定理 12），仅记录缺口。
