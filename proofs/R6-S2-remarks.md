# R6-S2 证明稿第 1 版的移出内容（附注、备注与修补记录）

> **不入审计，不得引用（D-1）。**
>
> **不入审计，不得引用**。本文件内容未经审计，其中已知含有被审计判为错误或无依据的陈述：§8‘有限偏移’第 2 小条（第 3 轮复审 n1，作为实数等式为假，反例 $W=(1,1)$、$\beta=\alpha/2$）；§8‘取整平局’第 2 小条中‘$y_{n_k}$ 也远离 $\pm1/2$’（n2，无依据）；第 1 轮修补记录 M4 中以 $8K\tau_{\max}$ 写的界（第 2 轮复审 m1，为假，已在第 2 轮修补记录中更正）。这些内容只作历史保留，不作更正。
>
> 已知错误或无依据的位置（本文件行号）：[n1] remarks L40（§8“有限偏移”第 2 小条：所写关系只在模 1 下成立，作为实数等式为假；反例 $W=(1,1)$、$\beta=\alpha/2$）；[n2] remarks L35（§8“取整平局”第 2 小条：“$y_{n_k}$ 也远离 $\pm1/2$”无推导支撑）；[M4] remarks L88（第 1 轮修补记录 M4：以 $8K\tau_{\max}/\min(A_k,A_{k+1})$ 写的界为假，即 $\tau_{\max}$ 版；第 2 轮修补记录 m1 处有更正）。
>
> 过时说法：块 B2 称 proofs/R6-S7-mstar.md “同为待审稿”，已过时，R6-S7 现为 `L3_FORMALIZED`（PLAN_GRAPH 节点表）；照搬时未改。
>
> 来源与搬移方式：v1 是 git 提交 92cb848 中的 `proofs/R6-S2.md`（第 1 版证明稿）。下列各块按 PLAN_GRAPH §“R6-S2 路线重构”D-1、D-3 原文整体搬移，未改一字；块内的节号、步骤号与“本文”均指 `proofs/R6-S2.md` 第 1 版。块之间只插入 HTML 注释形式的定界行；去掉定界行后，正文等于各块按原顺序的拼接（由 `experiments/R6-S2/scope_v2_diff_check.py` 机械核对）。本文件不提供给 R6-S2 第 2 版的审计员（D-4）。

| 块 | v1 原起止行 | 内容 | 本文件位置 |
|---|---|---|---|
| B1 | v1 L211–L213 | §5.5 末尾附注（另一种读法） | remarks L23–L25 |
| B2 | v1 L330–L330 | §7.3 指向 proofs/R6-S7-mstar.md 的子条 | remarks L28–L28 |
| B3 | v1 L334–L364 | §8 全节 | remarks L31–L61 |
| B4 | v1 L368–L376 | §9 全节（R1、R2、R3） | remarks L64–L72 |
| B5 | v1 L401–L473 | 修补记录（第 1 轮）（第 2 轮）（第 3 轮） | remarks L75–L147 |

<!-- REMARKS-BODY-BEGIN -->
<!-- BLOCK B1 BEGIN v1:L211-L213 §5.5 末尾附注（另一种读法） -->
- **附注（不属于对陈述的证明；陈述已固定为规范标签）**：若把 (b) 中的 $r_k$ 换成任意满足 (b) 第一条的序列 $r'_k$，(c) 依然成立。
  - （⇐）的论证只用到 (b) 第一条与 $r'_k=0$，照搬即可。
  - （⇒）：当 $\beta\in\mathbb Z\alpha+\mathbb Z$ 时 $y_n\to0$，(b) 第一条（$i=1$，$c_1=1$）给出 $d_K(r'_k)\to0$，所以 $r'_k=0$ 最终成立。$\ell=0$ 时 $r'_k$ 只能为 0。
<!-- BLOCK B1 END -->
<!-- BLOCK B2 BEGIN v1:L330-L330 §7.3 指向 proofs/R6-S7-mstar.md 的子条 -->
  - 另一条独立的纯组合路线给出更强的 $\nu(W)\ge1/2$，见 proofs/R6-S7-mstar.md（同为待审稿，本证明**不依赖**它）。
<!-- BLOCK B2 END -->
<!-- BLOCK B3 BEGIN v1:L334-L364 §8 全节 -->
## 8. 关于取整平局、有限偏移与一致性（任务要求的三处注意点）

- **取整平局**：
  - $y_n$ 的平局不影响 $\lvert y_n\rvert$ 与 $R_n$（§2.1）。
  - 规范标签由 S1 陈述对一切 $k\ge1$ 定义，平局任取。本文只在 $k\ge k_1$ 处使用它与 $t_k$，此时 $Ky_{n_k+1}$ 离整数的距离 $<1/2$，$y_{n_k}$ 也远离 $\pm1/2$，最近整数唯一；$y_{n_k+1}$ 自身的平局只改变 $\operatorname{round}(Ky_{n_k+1})$ 一个 $K$ 的倍数，不改变标签。$k<k_1$ 处标签可能依赖平局取法，但只涉及有限个 $k$，不进入任何结论（详见 §5.2 末尾）。所以“结论对任何平局取法都成立”这一陈述要求得到满足。
  - 边的选取（步 4）平局只出现在有限个 $k$ 上，不影响任何 limsup。
  - 在 ν 的定义中，边代价 $\lvert t\rvert$ 在 $t$ 与 $-t$ 处相同，所以 $d=K/2$ 时 $t=\pm1/2$ 两种选法代价相同，与 skeptic 的定义审查一致。
- **有限偏移**：
  - S1 的全部结论和 S2 的证明都只涉及 $k\to\infty$ 的极限或 limsup，有限个初始块（包括 §5.6 中只为“标签对齐”而改动的 $T'_1$，以及标签可能依赖平局取法的 $k<k_1$）都不影响结论。
  - 对 $\beta$ 加上格元素 $u\alpha+v$，会使 $y_n$ 最终改变 $u\varepsilon_n$。§5.6 的构造本身不需要这一点，§5.5 已经单独处理了格元素的情形。
- **$O(1/A)$ 误差的一致性**：
  - 每个 β 的所有误差项都有显式上界。
    - §5.6 中为 $4T_{\max}/A_{k-1}$、$4T_{\max}/A_{k+1}$、$4T_{\max}/A_k$（除以 $K$）。
    - §5.1–5.4 中，对 $k\ge k_0$（$k_0$ 依赖 β，由 §5.1 取定：$R_n\le\mathcal K+1$ 对 $n\ge n_{k_0}$ 成立），实际的界如下（逐条由 §5.1–5.4 的推导读出，并用 D2 的 $\theta_{n_k}<1/A_k$）：
      - (E1) $\lvert y_{n_k}\rvert<(\mathcal K+1)/A_k$，$\lvert t_k\rvert<\mathcal K+1$（§5.1、§5.4）。两式在 $y_{n_k}=0$ 时仍严格成立：第一式为 $\lvert y_{n_k}\rvert\le(\mathcal K+1)\theta_{n_k}<(\mathcal K+1)/A_k$，第二式为 $\lvert t_k\rvert\le(A_k\theta_{n_k})(\mathcal K+1)<\mathcal K+1$，严格性都只来自 $\theta_{n_k}<1/A_k$（D2）与 $\mathcal K+1\ge1>0$，不依赖 $y_{n_k}\ne0$。
      - (E2)（$\ell\ge1$，§5.2）$\operatorname{dist}(Ky_{n_k+1},\mathbb Z)\le\lvert y_{n_{k+1}}\rvert+K_{[2,\ell]}\lvert y_{n_k}\rvert<(\mathcal K+1)\bigl(1/A_{k+1}+K_{[2,\ell]}/A_k\bigr)$。对 $k\ge k_1$，左边就是 $\lvert Kg_k\rvert$（§5.2 的 $g_k$）。
      - (E3)（$\ell\ge1$，$k\ge k_1$，$1\le i\le\ell$，§5.3）$\bigl\lvert\lvert y_{n_k+i}\rvert-d_K(c_ir_k)/K\bigr\rvert\le\lvert e_{k,i}\rvert\le c_i\lvert g_k\rvert+K_{[2,i-1]}\lvert y_{n_k}\rvert<(\mathcal K+1)\Bigl(\dfrac{c_i}K\bigl(\dfrac1{A_{k+1}}+\dfrac{K_{[2,\ell]}}{A_k}\bigr)+\dfrac{K_{[2,i-1]}}{A_k}\Bigr)$。
      - (E4)（$\ell\ge1$，$k\ge k_1$，§5.4）$\operatorname{dist}\bigl(t_{k+1}-(r_{k+1}-\sigma r_k)/K,\mathbb Z\bigr)\le\lvert g_{k+1}\rvert+\lvert e_{k,\ell}\rvert$，再由 (E2)(E3)（$i=\ell$，$c_\ell=\sigma$）得到显式界 $(\mathcal K+1)\Bigl(\dfrac1K\bigl(\dfrac1{A_{k+2}}+\dfrac{K_{[2,\ell]}}{A_{k+1}}\bigr)+\dfrac{\sigma}K\bigl(\dfrac1{A_{k+1}}+\dfrac{K_{[2,\ell]}}{A_k}\bigr)+\dfrac{K_{[2,\ell-1]}}{A_k}\Bigr)$。
      - (E4₀)（$\ell=0$，$k\ge k_0$，§5.4“耦合（ℓ = 0）”）$\operatorname{dist}(t_{k+1},\mathbb Z)\le\lvert y_{n_{k+2}}\rvert+\lvert y_{n_k}\rvert<(\mathcal K+1)(1/A_{k+2}+1/A_k)$。这里只用到 (E1) 对指标 $k$ 与 $k+2$（均 $\ge k_0$）的第一式，不涉及标签，也不需要 $k_1$（$\ell=0$ 时 §5.2 没有定义 $k_1$）。严格性来自 (E1)，在 $y\equiv0$ 时也成立。
      - （修补第 3 轮补，退化情形）(E2)–(E4) 的最后一个 “$<$” 都继承自 (E1) 第一式的严格性：(E2) 中 $\lvert y_{n_{k+1}}\rvert<(\mathcal K+1)/A_{k+1}$ 严格，$K_{[2,\ell]}\lvert y_{n_k}\rvert\le K_{[2,\ell]}(\mathcal K+1)/A_k$；(E3) 中 $c_i\lvert g_k\rvert=(c_i/K)\lvert Kg_k\rvert$ 严格小于 $(c_i/K)$ 乘 (E2) 的界（$c_i\ge1$），而 $K_{[2,i-1]}\lvert y_{n_k}\rvert\le K_{[2,i-1]}(\mathcal K+1)/A_k$（$i=1$ 时 $K_{[2,0]}=0$，两边都为 0）；(E4) 中 $\lvert g_{k+1}\rvert$ 与 $\lvert e_{k,\ell}\rvert$ 两项都严格。因此在 $\beta\in\mathbb Z\alpha+\mathbb Z$（包括 $y\equiv0$、$\mathcal K=0$）时，(E1)–(E4₀) 的严格不等号全部仍然成立。
    - 与审计建议的写法对照：形如 $(\mathcal K+1)(1/A_{k+1}+K_{[2,\ell]}/A_k)$ 的量**恰好**是 (E2)，即标签误差 $\lvert Kg_k\rvert$ 的界；(E3)(E4) 的实际界形式不同（多出系数 $c_i/K$、$\sigma/K$ 以及 $K_{[2,i-1]}/A_k$ 等项），所以上面按实际推导分别写出，没有统一成一个式子。这些不等式（含严格性）的数值旁证见 `experiments/R6-S2/repair2_m1_m4_bounds.py` Part B（B1–B4，输出 `.out`），它不进入证明。
  - 本证明**从不**交换关于 β 的极限，也不需要对 β 一致：$\mathcal K_\alpha(\beta)$ 和 $c^*$ 的下界是逐 β 证明的（7.1），上界只用到一个具体的 β（7.2）。
  - 特别地，“标签**最终**正确”（§5.6 (d3) 末尾及 S1(d)）的收敛是**逐 β 的**：标签从某个 $k$ 起等于给定的 $r_k$，这个 $k$ 由何时 $\lvert Kg'_k\rvert<1/2$ 控制。由 (d3)（$n=n_k+1$，$\ell\ge1$），$\lvert Kg'_k\rvert<1/2$ 是标签在第 $k$ 块正确的一个**充分**条件（不是必要条件），其中 $g'_k:=E^{\rm past}_{n_k+1}+E^{\rm fut}_{n_k+1}$ 是 (d3) 中的量（不是 §5.2 的 $g_k$，见 (d4) 的注），并且
    $$\lvert Kg'_k\rvert\le K\lvert E^{\rm past}_{n_k+1}\rvert+K\lvert E^{\rm fut}_{n_k+1}\rvert\le\frac{4T_{\max}}{A_k}+\frac{4T_{\max}}{A_{k+1}}\le\frac{8T_{\max}}{\min(A_k,A_{k+1})}.$$
    这里 $T_{\max}=\max\bigl(\sup_k\lvert T_k\rvert,\lvert T'_1\rvert\bigr)$ 是 §5.6 中**含 $T'_1$ 修正**的量，$T_k=K\tau_k$，$T'_1=T_1+\sigma\tilde r_0$。用 τ 表示时有两种正确写法：
    - (τ′) 用修正后的序列 $\tau'_k=T'_k/K$（§5.6）：由 (d3) 开头的注，各上界在 $T_{\max}$ 换成 $T'_{\max}=K\tau'_{\max}$ 后仍成立，所以 $\lvert Kg'_k\rvert\le8K\tau'_{\max}/\min(A_k,A_{k+1})$，其中 $\tau'_{\max}=\sup_k\lvert\tau'_k\rvert$。
    - (τ) 用原序列 $\tau_{\max}=\sup_k\lvert\tau_k\rvert$：有 $T_{\max}\le K\tau_{\max}+\sigma(K-1)$。证：$\sup_k\lvert T_k\rvert=K\tau_{\max}\le K\tau_{\max}+\sigma(K-1)$（因为 $\sigma\ge1$，$K\ge1$）；又 $\tilde r_0\in[0,K)$ 是整数，故 $0\le\tilde r_0\le K-1$，于是 $\lvert T'_1\rvert\le\lvert T_1\rvert+\sigma\tilde r_0\le K\tau_{\max}+\sigma(K-1)$。所以 $\lvert Kg'_k\rvert\le8\bigl(K\tau_{\max}+\sigma(K-1)\bigr)/\min(A_k,A_{k+1})$。其中 $T_{\max}\le K\tau_{\max}+\sigma(K-1)$ 可以取等号（例如 $\tau_1=\tau_{\max}\ge0$、$\tilde r_0=K-1$ 时 $T'_1=K\tau_{\max}+\sigma(K-1)$），所以这一步不能再改进为 $T_{\max}\le K\tau_{\max}$。
    - **不能**写成 $8K\tau_{\max}/\min(A_k,A_{k+1})$（第 1 轮修补记录 M4 中的写法是错的）：$\lvert T'_1\rvert$ 可达 $K\tau_{\max}+\sigma(K-1)$，而 $K\tau_{\max}$ 可以是 $O(1)$。反例 $W=(1,9,9)$，$K=91$，$\sigma=10$，$r_0=90$，$r_k=0$，$\tau_1=10/91$，$A_k=1000+k$：$k=1$ 时 $\lvert Kg'_1\rvert\approx0.818$，大于 $8K\tau_{\max}/\min(A_1,A_2)\approx0.0799$。见 `experiments/R6-S2/reaudit_S2_6_M4_bound.py`/`.out` 与 `experiments/R6-S2/repair2_m1_m4_bounds.py` Part A（A1 对一切长度 $\le4$、分量 $\le5$ 的词穷举核对 $T_{\max}\le K\tau_{\max}+\sigma(K-1)$；A2 对审计反例和 12 个随机实例端到端核对 (τ′)(τ) 两种写法成立，并复现错误写法在审计反例的 $k=1$ 处失效），均为旁证，不进入证明。
    
    因此标签开始正确的位置依赖 $K$、$\sigma$、$T_{\max}$（即所给的 $\tau_k$ 以及 $r_0$ 的代表 $\tilde r_0$）以及 $(A_k)$ 的增长；另外，§5.2 的 $k_1$ 也依赖 β（理由见 §5.2 末尾：它经由 $k_0$ 与 (a) 中的收敛选取）。这种收敛对 β（或对 $K$、$T_{\max}$）**不是一致的**；本文也不需要它一致。
  - 引理 B 的极限只依赖 α，与 β 无关。
<!-- BLOCK B3 END -->
<!-- BLOCK B4 BEGIN v1:L368-L376 §9 全节（R1、R2、R3） -->
## 9. 备注（不属于待证命题）

- **R1（校准，手算）**：
  - 若 $K=1$（例如 $W=\varnothing$、$W=(1)$），顶点集为 $\{0\}$，边为 $t\in\mathbb Z$，非平凡闭途径必含 $\lvert t\rvert\ge1$，所以 $\nu=1$。
  - $W=(1,1)$：$K=K(1,1)=1\cdot1+1=2$；$c_1=1$，$c_1'=K(1)=1$，$c_2=K(1)=1$，$c_2'=1$，$\sigma=1$。
  - $v(1)=\max(d_2(1)/1,d_2(1)/1)=1$。任何经过顶点 1 的闭途径代价 $\ge1$；只停在顶点 0 的非平凡闭途径必含 $t\in\mathbb Z\setminus\{0\}$，代价 $\ge1$。再由 (C0)，$\nu((1,1))=1$。
  - 这与 skeptic 的 T1 表（`experiments/R6-S2/R6_R6-S2_T1_nu_table.tsv`）一致。
- **R2**：引理 0 只证明了 KL 1991 Thm 1 的一个方向，并且是严格不等式版本。KL 的完整陈述（含“$\le\theta_n/4$”的等号情形与反方向）本文**未核到原文**，也没有使用。
- **R3**：若 proofs/R6-S7-mstar.md 通过审计，则 $\nu(W)=\min(1,m^*(W))$ 对一切 $K\ge2$ 的 $W$ 成立，且 $\nu(W)\ge1/2$。与本文合起来，在块 Hurwitz 类上一致有 $c^*\ge1/2$。这会改变 R6-S4 的状态，应由 strategist 处理；本文不改状态文件。
<!-- BLOCK B4 END -->
<!-- BLOCK B5 BEGIN v1:L401-L473 修补记录（第 1 轮）（第 2 轮）（第 3 轮） -->
## 修补记录（第 1 轮）

> R6 旁支 Step 4，隔离 skeptic 裁决 MINOR_FIX 后的第 1/3 轮修补。只改本文件；PLAN_GRAPH 中的陈述与状态文件未动，未 git commit。

- **M1（§0.1 漏抄“已知下界”条）**：已在 §0.1 补抄 PLAN_GRAPH §S.1 的“已知下界”条（KL 1991 Thm 1 的转述），逐字，位置与 S.1 原顺序一致（第 5 条）。其后加 prover 注“本证明未使用此条”，并指向 §4 引理 0 / 推论 0′ 的自证。§0.1 标题改为“逐字，共 7 条”。已用脚本逐行比对 S.1 的 7 条与 S.2 中 S1、S2 的条目，均与 PLAN_GRAPH 现行文本逐字一致。
- **M2（S1 陈述与规范标签）**：
  - §0.2 按 PLAN_GRAPH 现行版本（2026-11-27 R6 旁支 Step 4，按审计 M2 加入规范标签定义）重新逐字抄录 S1 的陈述及 (a)–(d)。
  - §0.4 的 I1 改为说明“规范标签已写入陈述（PLAN_GRAPH 2026-11-27 M2）”，不再作为解释性约定；I2、I3 仍为解释性约定。§0.4 引言、[GAP] 清单说明与“本证明没有做到什么”中对 I1–I3 的提法同步改为 I2、I3。
  - §5.2 标题改为“S1 陈述中的定义”，并明确：陈述对一切 $k\ge1$ 定义 $r_k$（平局任取）；$k\ge k_1$ 时 $\operatorname{round}(Ky_{n_k+1})$ 不涉及平局，$r_k=s_k\bmod K$。新增“平局与一致性”段，处理两类平局：$y_{n_k+1}$ 自身的平局只把 $\operatorname{round}(Ky_{n_k+1})$ 改变 $\pm K$，标签不变；$Ky_{n_k+1}$ 的平局只可能出现在有限个 $k<k_1$ 上。由于 (b)(c)(d) 只涉及极限或“最终”性质，结论对任何平局取法都成立，与陈述的规定一致。原文“标签尚未定义的 $k<k_1$”（§8）改为“标签可能依赖平局取法的 $k<k_1$”，因为按现行陈述标签对一切 $k$ 都有定义。
  - §5.5 末尾的“另一种读法”改称“附注（不属于对陈述的证明）”。
  - §5.6 (d3) 末尾补充：$\operatorname{round}(Ky_{n_k+1})$ 在 $k$ 充分大时无平局，且与 $y_{n_k+1}$ 的平局取法无关；(d4) 补充 §5.6 的 $s_k$ 与 §5.2 的 $s_k$ 是不同记号、模 $K$ 同余的说明，并明确结论针对陈述定义的 $r_k(\beta)$。
  - 其余用到标签之处（§7.1 步 1、§7.2 步 8 与步 10）已逐一核对，均只在 $k\ge k_1$ 或“$k$ 充分大”处使用规范标签，与陈述一致，未改动。
- **M3（引理 B 区间端点）**：§3 引理 B 的陈述改为开区间 $1/\theta_{n_k}\in(A_k,A_k+2)$。证明 B1 同步收紧：$\alpha_{n_k+1}\in(A_k,A_k+1)$（因为 $\alpha_{n_k+2}>a_{n_k+2}\ge1$，严格），于是 $A_k\theta_{n_k}\in(A_k/(A_k+2),1)$，并逐端写出严格不等式的来源。全文其余地方只用到 $\theta_{n_k}<1/A_k$ 与极限 $A_k\theta_{n_k}\to1$，不受影响。
- **M4（“最终正确”的收敛不一致）**：§8“一致性”段补充一条：标签“最终”正确是逐 β 的收敛。开始正确的位置由 $\lvert Kg_k\rvert<1/2$ 决定，而由 (d3)，$\lvert Kg_k\rvert<4T_{\max}/A_k+4T_{\max}/A_{k+1}\le8T_{\max}/\min(A_k,A_{k+1})$；以 $\tau_{\max}=\sup\lvert\tau_k\rvert$ 表示即 $8K\tau_{\max}/\min(A_k,A_{k+1})$，与审计所给的 $8T_{\max}\cdot K/A_k$ 量级一致。因此它依赖 $K$、$T_{\max}$ 与 $(A_k)$，并不一致；§5.2 的 $k_1$ 同样依赖 β。本文不需要一致性。
- **[GAP] 数**：本轮修补后仍为 0。本轮没有引入新的外部定理或数值常数；$8=4+4$ 由 (d3) 的两个显式上界相加得到，不是计算常数。

---

## 修补记录（第 2 轮）

> R6 旁支 Step 4，隔离复审员裁决 MINOR_FIX（m1–m4）后的第 2/3 轮修补。只改本文件，新增脚本 `experiments/R6-S2/repair2_m1_m4_bounds.py`（输出 `.out`）。PLAN_GRAPH 中的陈述与状态文件未动，未 git commit。第 1 轮修补记录原文保留未改，其中的错误在下面 m1 处注明更正。

- **m1（§8 中 $T_{\max}$ 与 $\tau_{\max}$ 的混用；局部错误）**：
  - **更正第 1 轮修补记录 M4**：M4 段写的“$T_{\max}=\sup_k\lvert K\tau_k\rvert$（含 $T'_1$ 修正）”以及“以 $\tau_{\max}$ 表示即 $8K\tau_{\max}/\min(A_k,A_{k+1})$，与审计所给的 $8T_{\max}\cdot K/A_k$ 量级一致”是错的。原因：$T_{\max}$ 含 $T'_1=T_1+\sigma\tilde r_0$，$\lvert T'_1\rvert$ 可达 $K\tau_{\max}+\sigma(K-1)$，而 $K\tau_{\max}$ 可以是 $O(1)$。复审员的反例（$W=(1,9,9)$，$k=1$ 处 $\lvert Kg'_1\rvert\approx0.818>0.0799$）已由 `repair2_m1_m4_bounds.py` Part A2 复现。M4 段原文按要求不改写。
  - §8“一致性”第 3 条重写：明确 $T_{\max}=\max(\sup_k\lvert T_k\rvert,\lvert T'_1\rvert)$ 含修正；给出两种正确的 τ 写法，两种都写出：
    - (τ′) 在 §5.6 定义修正序列 $\tau'_k:=T'_k/K$ 与 $\tau'_{\max}$，并在 (d3) 开头加注：$T_{\max}$ 只经由 $\lvert x_j\rvert=\lvert T'_j\rvert\le T_{\max}$ 进入，所以各上界对 $T'_{\max}=K\tau'_{\max}$ 也成立，从而 $\lvert Kg'_k\rvert\le8K\tau'_{\max}/\min(A_k,A_{k+1})$。
    - (τ) $T_{\max}\le K\tau_{\max}+\sigma(K-1)$，并给出证明（三角不等式与 $0\le\tilde r_0\le K-1$、$\sigma\ge1$），指出可取等号。脚本 Part A1 在一切长度 $\le4$、分量 $\le5$ 的词（781 个）以及全部 $r_0,r_1$ 和若干 $T_1$ 上做了精确整数穷举，共 297 571 176 例，无违反，其中 290 056 例取等号。Part A2 在审计反例和 12 个随机实例上端到端核对了 (τ′)(τ) 两种上界都成立，并确认错误写法在审计反例的 $k=1$ 处失效（随机实例 8 也在 $k=1$ 处失效）。
  - 删去“与审计意见所说的 $8T_{\max}\cdot K/A_k$ 量级一致”这一比较。
  - 顺带改正同一句中的两处措辞：“这个 $k$ 取决于何时 $\lvert Kg_k\rvert<1/2$”改为“$\lvert Kg'_k\rvert<1/2$ 是标签正确的**充分**条件”（它不是必要条件：审计反例在 $k=1$ 处该量 $>1/2$，标签也确实错了；但一般情况下该量 $\ge1/2$ 并不意味着标签错）；依赖项中补上 $\sigma$ 与 $\tilde r_0$。
  - 附带（不在 m1–m4 清单内，同属这一处）：同一段末尾原有的“同理 §5.2 的 $k_1$ 依赖 β”含禁用语“同理”，已改为直接给出理由（见 §5.2 末尾）。
  - 附带（不在 m1–m4 清单内，同属这一处）：(d3) 中的严格不等式在 $T'_{\max}=0$（即 $\beta=0$）时两边都为 0，不成立。已在 (d3) 开头的注中写明此时读作 $\le$，后文只用到 $\le$ 形式。
- **m2（§5.2 与 §5.6 (d3) 的 $g_k$ 含义不同）**：
  - §5.6 (d3) 末尾的量改名为 $g'_k$，并显式定义 $g'_k:=E^{\rm past}_{n_k+1}+E^{\rm fut}_{n_k+1}$、$z_k:=-\operatorname{round}(q_{n_k+1}\beta)$；补写 $\lvert Kg'_k\rvert\le4T_{\max}/A_k+4T_{\max}/A_{k+1}$，并标明这一段只针对 $\ell\ge1$（此时 $n_k+1$ 属于第 $k$ 块）。
  - §5.2 在 $g_k$ 的定义后加一句，说明它对一般 β 定义，$\lvert Kg_k\rvert=\operatorname{dist}(Ky_{n_k+1},\mathbb Z)$，并指向 (d4) 的注。
  - (d4) 的注扩充：说明 $g'_k$ 与 $g_k$ 的区别；在 $\lvert Kg'_k\rvert<1/2$ 且 $k\ge k_1$ 时二者相等（此时 §5.2 的 $s_k=P^{(k)}_{n_k+1}+Kz_k$），一般情况下不必相等。
  - §8 第 3 条中的引用全部同步为 $g'_k$；§8 第 1 条 (E2)(E3)(E4) 讲的是 §5.2–5.4 中一般 β 的量，保留 $g_k$，并注明“§5.2 的 $g_k$”。
- **m3（(d4) 缺 ℓ = 0 的说明）**：(d4) 新增一条：$\ell=0$ 时 $K=1$，$\mathbb Z/1$ 只有一个元素，给定的 $r_k$ 与规范标签都等于它，“标签最终正确”平凡成立；(d3) 中针对 $n_k+1$ 的论证在这种情形不需要。$t_k-\tau_k\to0$ 由 (d3) 中 $n=n_k$ 的论证给出，那段只用到 D1、D2、D4 以及 $q_{n_k}\ge q_{n_{k-1}+1}$、$q_{n_{k+1}}\ge q_{n_k+1}$。$\ell=0$ 时这两个不等式取等号，因此不依赖 $\ell\ge1$。
- **m4（§8 第 1 条只写了“由 $\mathcal K+1$、$W$ 的连续子以及 $A_k$ 决定”）**：
  - 改写前先逐条核对 §5.1–5.4 的推导。结论：审计建议的式子 $(\mathcal K+1)(1/A_{k+1}+K_{[2,\ell]}/A_k)$ **只与**标签误差 $\operatorname{dist}(Ky_{n_k+1},\mathbb Z)$（$k\ge k_1$ 时即 $\lvert Kg_k\rvert$）的实际界一致。这个界由 §5.2 的同余 $Ky_{n_k+1}\equiv y_{n_{k+1}}-K_{[2,\ell]}y_{n_k}$ 与 $\lvert y_{n_j}\rvert\le(\mathcal K+1)\theta_{n_j}<(\mathcal K+1)/A_j$ 得到。§5.3 的 $e_{k,i}$ 与 §5.4 的耦合误差的实际界形式不同。
  - 因此按“不一致就写实际的界”的要求，§8 第 1 条改为：对 $k\ge k_0$（$k_0$ 依赖 β），逐条列出 (E1)–(E4) 的显式界。(E1) 是 $\lvert y_{n_k}\rvert$ 与 $\lvert t_k\rvert$；(E2) 是标签误差，即审计建议的式子；(E3) 是 (b) 第一条的误差；(E4) 是 (b) 第三条的耦合误差，含 $\ell=0$ 的情形。每条注明适用范围（$\ell\ge1$、$k\ge k_1$）及其出处小节。
  - 脚本 Part B 在 10 个随机词上，对一般随机 β 与 §5.6 构造的 β 共 1080 项检查 B1–B4（用实际出现的 $R_n$ 代替 $\mathcal K+1$），无违反。它只作旁证，不进入证明。
- **[GAP] 数**：本轮修补后仍为 0。新写的不等式（(τ) 的 $T_{\max}\le K\tau_{\max}+\sigma(K-1)$ 以及 (E1)–(E4)）都在正文中由符号推导给出。数值只用于旁证，脚本为 `experiments/R6-S2/repair2_m1_m4_bounds.py`，输出 `.out`，末行为 `ALL CHECKS PASSED`。反例中的数值 $0.818$、$0.0799$ 取自 `reaudit_S2_6_M4_bound.out`，并由本脚本 Part A2 复现。本轮没有引入外部定理。

---

## 修补记录（第 3 轮）

> R6 旁支 Step 4，隔离复审员裁决 MINOR_FIX（m1–m4）后的第 3/3 轮修补，也是最后一轮。只改本文件，新增旁证脚本 `experiments/R6-S2/repair3_degenerate_strict.py`（输出 `.out`）。PLAN_GRAPH 中的陈述与状态文件未动，未 git commit。论证结构未改，只改不等号或补充退化情形的说明。第 1、2 轮修补记录原文保留未改。

- **m1（§5.4“有界性”）**：$\lvert t_k\rvert=(A_k\theta_{n_k})R_{n_k}<R_{n_k}$ 改为 $\le R_{n_k}$，并在括注中写明 $y_{n_k}=0$（例如 $\beta\in\mathbb Z$）时两边都为 0。
  - 后文是否依赖这里的严格号：逐处核对，**不依赖**。§5.4 本身只用到“$\le\mathcal K+1$”（有界性）。§7.1 步 3、§5.5（⇐）、§5.6 (d4) 用的是等式 $R_{n_k}=\lvert t_k\rvert/(A_k\theta_{n_k})$，不是这个不等式。
  - §8 (E1) 的 $\lvert t_k\rvert<\mathcal K+1$ 仍然严格成立。我在 §5.4 末尾和 (E1) 中各补了一句推导：$\lvert t_k\rvert\le(A_k\theta_{n_k})(\mathcal K+1)<\mathcal K+1$，严格性只来自 $A_k\theta_{n_k}<1$ 与 $\mathcal K+1\ge1>0$。
- **m2（§5.5（⇒）两处）**：$\lvert u\varepsilon_n\rvert<\lvert u\rvert/q_{n+1}$ 与 $\lvert t_k\rvert<\lvert u\rvert/q_{n_k}$ 都改为 $\le$。括注写明：$u\ne0$ 时严格，$u=0$ 时两边都为 0。另外单列一句：$u=0$（即 $\beta=v\in\mathbb Z$）时，对一切 $n$ 都有 $y_n=0$、$R_n=0$、$t_k=0$，结论平凡。
  - 顺带把“对充分大的 $n$，$y_n=u\varepsilon_n$”的理由写全，这不是不等号修改，只是补出原先省略的一步：$\lvert u\varepsilon_n\rvert<1/2$ 最终成立，所以 $q_n\beta$ 的最近整数唯一，等于 $up_n+vq_n$；并写出 $R_n=\lvert u\rvert/q_n$。
  - 后文是否依赖这里的严格号：**不依赖**。（⇒）只用到这两个量 $\to0$。§7.2 步 10 引用的是 (c)（⇒）的逆否结论，不是这两个不等式。
- **m3（§8 (E4) 的适用范围）**：(E4) 条目只保留 $\ell\ge1$、$k\ge k_1$ 的情形。$\ell=0$ 的界单列为 **(E4₀)**，标明适用范围是 $\ell=0$、$k\ge k_0$，出处为 §5.4“耦合（ℓ = 0）”。补充说明：它只用到 (E1) 第一式在指标 $k$ 与 $k+2$ 处的形式，不需要 $k_1$；$\ell=0$ 时 §5.2 也没有定义 $k_1$。
- **m4（(d3) 开头的措辞）**：“全部是显式上界，只依赖 $T_{\max}$ 和 $K$”改为“全部是显式上界，其中的常数只依赖 $T_{\max}$、$K$，界本身还含 $q_n$ 或 $A_k$”。
- **全文扫描（退化情形 $\beta\in\mathbb Z\alpha+\mathbb Z$：$y_n\equiv0$、$u=0$、$t_k=0$、$\mathcal K=0$；以及 §5.6 中 $\beta=0$ 的构造）**：我用脚本列出正文（§0–§9）中每一个 “$<$”“$>$”，逐处判断。结果如下。
  - **会变假、已修正的**：只有 m1、m2 列出的三处，即 §5.4 一处、§5.5（⇒）两处。除此之外没有发现新的会变假的严格号。
  - **在退化情形下仍然成立、未改的**（逐处理由）：
    - D2 的 $\theta_n<1/a_{n+1}$、$\lvert\varepsilon_n\rvert<1/q_{n+1}$，以及 B1、B2 中关于完全商的严格号：只涉及 α，与 β 无关。
    - 引理 0 的 0.2：$\lvert y\rvert<\theta/4$ 是假设，$0<\theta/4$ 恒成立；$<3/4$ 来自 $\theta<1$。推论 0′ 只是 limsup 推最终成立。
    - §5.1 的 $\lvert y_{n_k}\rvert\le(\mathcal K+1)\theta_{n_k}<(\mathcal K+1)/A_k$：严格性来自 $\theta_{n_k}<1/A_k$ 与 $\mathcal K+1>0$。
    - §5.2、§5.6 (d3) 末尾以及 §8 中的“距离 $<1/2$”“$\lvert Kg'_k\rvert<1/2$”：它们都是选取 $k_1$ 或“$k$ 充分大”的条件，在 $y\equiv0$ 时左边为 0，仍然成立。
    - §5.5（⇐）、§5.6 (d4)、§7 中的 “$>0$”“$<\infty$”“$R_n<1/4$ 最终成立”：都不受影响。
    - §8 (E1)–(E4)、(E4₀)：严格性都继承自 (E1) 第一式，在 $y\equiv0$、$\mathcal K=0$ 时仍然严格成立。我在 (E4₀) 之后补了一条“退化情形”说明，逐条写出严格性的来源。
  - **已被第 2 轮注覆盖、本轮只把说明写精确的**：§5.6 (d3) 中以 $T_{\max}$ 写出的严格上界在 $T_{\max}=0$ 时失效，以 $T'_{\max}$ 写出时在 $T'_{\max}=0$ 时失效。第 2 轮的注已规定“$T'_{\max}=0$ 时读作 $\le$”。本轮在该注末尾补充三点：(i) 准确的失效条件；(ii) $T_{\max}=0\Rightarrow T'_{\max}=0$，所以两种情形都被覆盖；(iii) $T_{\max}>0$ 而 $T'_{\max}=0$ 是可能的（$\beta=0$），这时以 $T_{\max}$ 写的严格形式仍成立。
- **数值旁证**（不进入证明）：`experiments/R6-S2/repair3_degenerate_strict.py`，输出 `.out`，末行 `ALL CHECKS PASSED`。
  - Part A：取 $W\in\{(1,9,9),(2),()\}$，$(u,v)\in\{(0,3),(0,0),(1,0),(-2,1),(5,-7)\}$，各 11 块。修正后的 $\le$ 形式全部成立；旧的严格形式恰好在 $u=0$ 时全部失效，$u\ne0$ 时全部成立。
  - Part B：取 $W\in\{(1,9,9),(2),(3,1),()\}$，在格点 β 上取 $\mathcal K+1=1$，核对 (E1)–(E4)、(E4₀) 的严格形式，无违反。
  - Part C：取 $W=(1,9,9)$、$r_0=90$、$T_1=-900$。此时 $T'_1=0$、$T_{\max}=900$、$T'_{\max}=0$、$\beta=0$。复现结果：以 $T_{\max}$ 写的严格形式成立，以 $T'_{\max}$ 写的严格形式失效，$\le$ 形式成立。
  - α 取 $[0;A_1,W,A_2,W,\dots]$，$A_k=10+k$，截断到 60 块，mpmath 400 位；$u=0$ 时 $y_n$ 按精确整数 0 处理。
- **[GAP] 数**：本轮修补后仍为 0。本轮没有引入外部定理或新的数值常数。
<!-- BLOCK B5 END -->
