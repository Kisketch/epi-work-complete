# R6-S7（暂定编号）证明稿：$m^*(W)\ge1/2$，从而 $\nu(W)=\min(1,m^*(W))\ge1/2$

> 角色：prover（R6 旁支 Step 3，可选项）。日期：2026-11-27。
> **旁支，与 $e+\pi$ 的无理性无关。**
> “R6-S7”只是总控在任务中给的文件名，PLAN_GRAPH.md 中尚无此节点；本文件不改任何状态文件。正确性由 skeptic 判定。
> 本证明是关于 S.1 中组合量 $v,\nu$ 的纯有限组合陈述，**不依赖** R6-S1/S2。它对 $c^*(\alpha)$ 的含义（推论 3）以 R6-S2 通过审计为前提，属类别 2 意义上的“依赖待审节点”。

## 陈述

**来源（逐字，PLAN_GRAPH.md “R6 旁支 Step 2 结果”）**：

> 结构性发现（待 strategist 纳入 DAG）：记 $m^*:=\min_{r\ne0}v(r)$。若 $m^*\ge1/2$，则 $\nu(W)=\min(1,m^*)$。范围内全部词都满足 $m^*\ge1/2$。若能**证明** $m^*\ge1/2$，则组合层面 $\inf_W\nu\ge1/2$；在 S2 成立的前提下，块 Hurwitz 类上一致有 $c^*\ge1/2>1/4$。

**待证命题（按总控指示：“尝试证明 $m^*\ge1/2$（组合引理）”）**。记号沿用 PLAN_GRAPH.md S.1，并见 proofs/R6-S2.md §0.1。

- **命题 1**：对每个块词 $W$，若 $K=K(W)\ge2$，则对一切 $r\in\mathbb Z/K$，$r\ne0$，都有 $v(r)\ge1/2$。即 $m^*(W)\ge1/2$。
- **推论 2**：对每个 $K(W)\ge2$ 的 $W$，$\nu(W)=\min(1,m^*(W))$；当 $K(W)=1$ 时，$\nu(W)=1$。因此对一切 $W$，$\nu(W)\ge1/2$。
- **推论 3（条件于 R6-S2）**：若 R6-S2 成立，则对一切块 Hurwitz 数 α，$c^*(\alpha)\ge1/2$。

## 依赖

- **上游节点**：命题 1 与推论 2 无；推论 3 依赖 R6-S2（状态 `L1_TESTED`，证明稿 proofs/R6-S2.md 待审）。
- **外部定理**：无。只用到 S.1 中连续子的定义，以及 proofs/R6-S2.md §2.4 的引理 (A2)（分裂恒等式与左递推）。该引理在那里已有完整的初等证明，并且不依赖任何连分数事实。
- **数值**：证明中没有需要计算的数值常数。
  - 有限核验脚本只作旁证（类别 4）：`experiments/R6-S2/R6_R6-S7_mstar_lemma_check.py`，输出 `experiments/R6-S2/R6_R6-S7_mstar_lemma_check.out`。
  - 脚本对 T1 表中 5888 个 $K\ge2$ 的词，逐一精确核对了下面的步 3、步 4、步 6 以及推论 2，全部通过。范围内 $m^*$ 的最小值为 $12/17$，在 $W=(5,1,1,1,5)$ 处取得，与 skeptic 的 T1 结果一致。

## 证明

设 $\ell\ge1$，因为 $K\ge2$ 蕴含 $\ell\ge1$：$\ell=0$ 时 $K=1$。

把 $c_j,c'_j$ 的定义延拓到 $0\le j\le\ell+1$：
- $c_j:=K_{[1,j-1]}$，于是 $c_0=0$，$c_{\ell+1}=K$；
- $c'_j:=K_{[j+1,\ell]}$，于是 $c'_0=K$，$c'_{\ell+1}=0$。

对 $1\le j\le\ell$，这与 S.1 的定义一致。

**步 1（两条递推）.** 对 $1\le j\le\ell$：
- (R) $c_{j+1}=w_jc_j+c_{j-1}$：这是 S.1 定义中的右递推，$j=1$ 时为 $c_2=w_1\cdot1+0$。
- (L) $c'_{j-1}=w_jc'_j+c'_{j+1}$：这是 R6-S2.md (A2b)，$K_{[j,\ell]}=w_jK_{[j+1,\ell]}+K_{[j+2,\ell]}$。

**步 2（分裂恒等式）.** 对 $0\le j\le\ell$，$c_{j+1}c'_j+c_jc'_{j+1}=K$。
- 对 $0\le j\le\ell-1$，令 $i=j+1\in[1,\ell]$，这就是 R6-S2.md (A2a)：$K=c_iK_{[i,\ell]}+K_{[1,i-2]}c'_i=c_ic'_{i-1}+c_{i-1}c'_i$。
- 对 $j=\ell$，左边为 $K\cdot1+c_\ell\cdot0=K$。
- 推论：各项非负，所以 $c_{j+1}c'_j\le K$（$0\le j\le\ell$）。

**步 3（$\gcd(p,K)=1$，其中 $p:=c'_1=K_{[2,\ell]}$）.**
- 由 (L)，$\gcd(c'_{j-1},c'_j)=\gcd(c'_j,c'_{j+1})$（$1\le j\le\ell$）。这是辗转相除的一步：$c'_{j-1}\equiv c'_{j+1}\pmod{c'_j}$。所以 $\gcd(c'_0,c'_1)=\gcd(c'_\ell,c'_{\ell+1})=\gcd(1,0)=1$。
- 又 $c'_0=K$，所以 $\gcd(K,p)=1$。
- 令 $\lambda\in\mathbb Z$ 满足 $\lambda p\equiv1\pmod K$。

**步 4（同余对偶）.** 对 $0\le j\le\ell+1$，$c_j\equiv(-1)^{j-1}\lambda c'_j\pmod K$。对 $j$ 归纳，同时验证 $j-1$、$j$ 两项：
- $j=0$：$c_0=0$，$c'_0=K\equiv0$。
- $j=1$：$c_1=1\equiv\lambda p=\lambda c'_1$。
- $j\to j+1$（$1\le j\le\ell$）：由 (L)，$c'_{j+1}=c'_{j-1}-w_jc'_j$，所以
  $$(-1)^{j}\lambda c'_{j+1}=(-1)^{j-2}\lambda c'_{j-1}+w_j(-1)^{j-1}\lambda c'_j\equiv c_{j-1}+w_jc_j=c_{j+1}\pmod K,$$
  其中同余号用归纳假设，最后一个等号用 (R)。

**步 5（改写顶点代价）.**
- 设 $r\in\mathbb Z$，$r\not\equiv0\pmod K$，令 $u\equiv\lambda r\pmod K$。由步 3，λ 模 K 可逆，所以 $u\not\equiv0$。
- 由步 4，$c_jr\equiv(-1)^{j-1}uc'_j\pmod K$。由于 $d_K$ 以 $K$ 为周期且为偶函数，对 $1\le j\le\ell$，$d_K(c_jr)=d_K(uc'_j)$。
- 选 $u$ 的代表使 $1\le\lvert u\rvert\le K/2$（$u\not\equiv0$ 时可以做到）。

**步 6（取指标）.** 由 (R) 与 $c_j\ge0$，序列单调：$c_1=1\le c_2\le\dots\le c_{\ell+1}=K$，因为对 $j\ge1$，$c_{j+1}=w_jc_j+c_{j-1}\ge c_j$。令 $J:=\min\{j\in[1,\ell+1]:c_j>2\lvert u\rvert\}$。

- **情形 (i)：集合为空**。此时 $K=c_{\ell+1}\le2\lvert u\rvert\le K$，所以 $\lvert u\rvert=K/2$。取 $j=\ell$：$c'_\ell=1$，$d_K(uc'_\ell)=d_K(u)=K/2$；而 $c_\ell c'_\ell=\sigma\le K$（单调性）。所以 $d_K(c_\ell r)/(c_\ell c'_\ell)\ge(K/2)/K=1/2$。
- **情形 (ii)：集合非空**。由于 $c_1=1\le2\le2\lvert u\rvert$，$J\ge2$。令 $j:=J-1\in[1,\ell]$，则 $c_j\le2\lvert u\rvert<c_{j+1}$。于是
  $$\tfrac12c_jc'_j\le\lvert u\rvert c'_j<\tfrac12c_{j+1}c'_j\le\tfrac K2,$$
  最后一步用步 2。所以 $0\le\lvert uc'_j\rvert<K/2$，从而 $d_K(uc'_j)=\lvert u\rvert c'_j$（当 $\lvert x\rvert\le K/2$ 时，$d_K(x)=\lvert x\rvert$）。因此
  $$\frac{d_K(c_jr)}{c_jc'_j}=\frac{\lvert u\rvert c'_j}{c_jc'_j}\ge\frac12.$$

两种情形都得到 $v(r)=\max_{1\le i\le\ell}d_K(c_ir)/(c_ic'_i)\ge1/2$。命题 1 证毕。$\square$

**步 7（推论 2）.** 设 $K\ge2$，$r^*\ne0$ 达到 $m^*$（$\mathbb Z/K\setminus\{0\}$ 有限且非空，所以最小值存在）。

- **上界 ①**：取 $r^*$ 处的自环，$t$ 取 $(r^*-\sigma r^*)/K+\mathbb Z$ 中绝对值最小的元素，则 $\lvert t\rvert\le1/2$。由 $r^*\ne0$，它不是平凡环。其代价为 $\max(v(r^*),\lvert t\rvert)\le\max(m^*,1/2)=m^*$（命题 1）。
- **上界 ②**：顶点 0 处 $t=1$ 的自环代价为 1（$v(0)=0$）。
- 由上界 ①②，$\nu\le\min(1,m^*)$。
- **下界**：任一非平凡闭途径 $C$，若经过某个 $r\ne0$，则 $\operatorname{cost}(C)\ge v(r)\ge m^*$。否则 $C$ 只经过顶点 0，其边都是 0 处的自环，$t\equiv0\pmod1$，即 $t\in\mathbb Z$；由于非平凡，某个 $t\ne0$，于是 $\operatorname{cost}(C)\ge1$。所以 $\nu\ge\min(1,m^*)$。
- 闭途径与简单圈两种读法给出同一个 ν，见 R6-S2.md (C3)。上面的论证对两种读法都直接成立。
- $K=1$ 时，见 R6-S2.md §9 R1。
- 由命题 1，$\nu(W)\ge\min(1,1/2)=1/2$。$\square$

**步 8（推论 3，条件于 R6-S2）.** 若 $c^*(\alpha)=\nu(W)$（R6-S2），则由推论 2，$c^*(\alpha)\ge1/2$。$\square$

## [GAP] 清单

无。命题 1 与推论 2 只用到连续子的初等恒等式，并且在本文或 R6-S2.md §2.4 中已证。推论 3 显式以 R6-S2 为前提，这不是缺口，而是条件。

## 本证明没有做到什么

- **常数不尖锐**：没有证明 $1/2$ 是 $\inf_Wm^*(W)$ 或 $\inf_W\nu(W)$ 的尖锐值。
  - 有限数据（类别 4，skeptic）给出的范围内最小值是 $12/17\approx0.7059$，扩展搜索约为 $0.7016$。
  - 因此真实的下确界很可能严格大于 $1/2$。它是多少仍然**开放**。
- **对 R6-S4 的影响**：若本文与 R6-S2 都通过审计，R6-S4 所问的“$\inf_W\nu(W)=1/4$？”在块 Hurwitz 类上的答案是**否**，因为 $\inf\ge1/2$。但这**不回答**“KL 常数 $1/4$ 在全体无理 α 上是否尖锐”。R6-S4 的状态应由 strategist 处理。
- **推论 3 是条件性的**：它依赖待审的 R6-S2。
- **与 $e+\pi$ 无关**：不涉及 π 或 $e+\pi$。
- **未形式化**：没有 Lean 形式化。
- **新颖性未判**：命题 1 可能是关于有理数连分数的某个经典事实的改写（未查证）。步 4 的对偶说明 $d_K(c_jr)/(c_jc'_j)$ 是有理数 $p/K$ 的有限 KL 比值。新颖性**未做任何检索**。
