# Perron / Stambul 新颖性核查记录（2026-11-21）

核查对象：paper1 backlog 任务 C（定理 8.5/8.6：显式周期 2B平方、2B|C|，阈值 j>B平方，相对 Perron (1954, 第33节) / Stambul (1997) 的新颖性）。
类别：第 5 类文献核查与复现。不涉及定理正确性，不构成对 e+pi 的推进判断。
引用纪律：书目与定理陈述只认本次实际打开的页面；没打开的一律标未核到。

## 内容身份说明（编号漂移）

backlog 所称定理 8.5/8.6 在现稿 paper1_e_plus_pi.tex 中对应（按内容同一性确认，现稿无 8.5/8.6 编号）：
- thm:explicit-period（第422行）：若 e+x=A/B，则 j>9B平方/4 时窗口长度 r_j 为奇数、r_j>=3，且 r_{j+2B平方}=r_j。
- thm:affine-window（第694行）：x=(A+Ce)/B 时 T=2B|C|，L=max(B,|C|)平方；j>L 时 r_{j+T}=r_j，W_{j+T}=(b_j+4G_j平方,S_j)，且 r_j=1 当且仅当 G_jG_{j+1}=T。
- 口径修正：阈值 j>B平方为简称。explicit-period 的真实阈值是 j>9B平方/4（=(3B/2)平方，比 B平方更强）；affine-window 的真实阈值是 L=max(B,|C|)平方，只在 |C|=1 时字面等于 B平方。

## 一句总判断

部分核实新颖（以本次实际打开全文为限）：Stambul (1997) 全文 8 页（pp.141-148，经 paper-search 开放获取链逐页打开）只含定性结论，即 R 类在整系数 Mobius 变换下封闭、周期仅存在性断言（q=(m2-m1)p1，无 B、C 显式函数）；全文无 2B平方、2B|C|、阈值 j>B平方（或 9B平方/4、max(B,|C|)平方）、无窗口计数 r_j、无首位增量 4M_j平方/4G_j平方、无 r_j=1 判据。Hetyei (2014，同行评审二手文献，本次打开其 arXiv 预印本 1211.2494) 明言 Perron 第33节对 quasi-period 长度问题保持沉默。Perron 第33节节内 Satz 编号因原书未能取得，维持未核到。
## 逐项对照表（检索日期均为 2026-11-21）

| 编号 | 断言 | 结论 | 证据（本次实测原文） | 来源 |
|---|---|---|---|---|
| 1 | Perron (1954) 卷一第33节内与显式周期/阈值相关的 Satz 编号 | 未核实 | DNB 目录页第三次打不开（本次 ECONNRESET；前两次 Transport error 见 perron_komatsu_davis_check_20261121.md 第3节）。Hetyei 只引第33节整体（Hurwitz 定理），未给节内 Satz 号；Stambul 只引 Perron 页码 127-131，未给 Satz 号。全文获取权威途径（建议线索，非已验证结论）：Teubner 1954 年 Bd.1 第 3 版实体书或馆际互借；DNB 记录页恢复后重试；Springer 重印本；WorldCat 联合目录。注意 archive.org 仅有 1913 年首版扫描，节号页码与第 3 版不可混用。 | https://d-nb.info/453736947/04（2026-11-21，ECONNRESET 未能打开） |
| 2 | Stambul (1997) 结果的准确陈述与定理号 | 已验证 | 全文仅 1 个未编号 Theorem（p.143）：Let xi be in R and h 为整系数 Mobius 变换，则 h(xi) 属于 R（正文证明处误写 Theorem 2，全篇仅此一定理）。另有 Lemma 1-3（pp.143-146）与 1 个未编号 Proposition（p.147，以 Fibonacci 数列为输入的 2xi 计算示例）。Perron 引文为参考文献 [7]：O. Perron, Die Lehre von den Kettenbruechen, Bd. 1, 3rd ed., Teubner, 1954, 110-138；p.141 正文：it follows from a theorem of O. Perron ([7], 127-131) that h(x) is also Hurwitzian. Moreover, the nonconstant polynomials in the quasi-periods of x and h(x) have the same degrees (see [10])。其中 [10] 为 Stambul 1994 年 Provence 大学博士论文（本次未追查其内容，标未核到）。书目级：CrossRef 确认题名 A generalization of Perron theorem about Hurwitzian numbers，Acta Arith. 80(2), 141-148, 1997。 | paper-search 之 read_semantic_paper（DOI:10.4064/aa-80-2-141-148）全文 pp.141-148（2026-11-21）；https://api.crossref.org/works/10.4064/aa-80-2-141-148（2026-11-21） |
| 3 | 显式周期 2B平方有先例 | 无先例（负搜索加 Stambul 全文核对；不是已证明不存在） | (a) Stambul 全文无任何 2B平方字样与显式周期公式；其 Lemma 1(i) 只给 mod D 最终周期性（Aj(k+1) 与 Aj(k) mod D 同余），周期 q=(m2-m1)p1 为存在性构造（p1=s 与 p 之积，s 为各周期公倍数），不是 B 的显式函数；p.147 终态序列 ultimately periodic 同样无显式界。(b) Hetyei 第1.2节：Hurwitz theorem provides also some estimate on the degrees ... remains silent however on the issue how the length of the period may be affected by the fractional linear transformation. (c) 关键词检索（OpenAlex 0 命中；Semantic Scholar 0 命中；arXiv top 命中为 Ramanujan 量、Tasoevian 闭式族等无关主题；CrossRef top 命中为 Rogers-Ramanujan、E1(x) 等无关主题），未见任何记录陈述 2B平方窗口周期。 | 同上 Stambul 全文；paper-search 之 read_arxiv_paper（1211.2494）（2026-11-21，本次打开的是 arXiv 预印本；其期刊出版信息 SIAM J. Discrete Math. 28 (2014) 系 paper1 自带引文，本轮未另行核验）；search_openalex、search_semantic、search_arxiv、search_crossref（2026-11-21，关键词加 top-10 有限覆盖） |
| 4 | 显式周期 2B|C| 有先例 | 无先例（同上口径） | Stambul 全文无 2B|C| 或任何以行列式绝对值 D 表出的显式窗口周期；其 transducer 状态集有限只推出存在最终周期（Lemma 1(iii) Br=Br+q），周期长无封闭式。Hetyei 的 remains silent 同样覆盖仿射（含 A 不为 0）情形的长度问题。检索覆盖同编号3。注：齐次情形 (m/n)e 的显式周期 d=mn 系 Matthews-Walters 1970 Thm 1(b)，paper1 正文已自行引为既有成果（affine 讨论段），属已承认先例、不在本轮复核范围。 | 同编号3 |
| 5 | 阈值 j>B平方（实际 9B平方/4；仿射 L=max(B,|C|)平方）有先例 | 无先例（同上口径，另加口径说明） | Stambul 全文无任何阈值型陈述；Lemma 1(ii) 的 Aj(k)>D 或常数是对每条序列的分类条件，不是统一阈值；Perron 第33节经 Hetyei 确认只给次数估计、无长度与阈值型定量界。检索覆盖同编号3。口径：backlog 的 j>B平方在 explicit-period 定理中实际为 j>9B平方/4，在 affine-window 中为 L=max(B,|C|)平方（|C|=1 时退化为 B平方）。 | 同编号3；tex 第427行（9B平方/4）、第698行（L 定义） |
## 文档与实现的差异

1. 编号漂移：backlog 的定理 8.5/8.6 在现稿中已无此编号，实际为 thm:explicit-period 与 thm:affine-window。后续引用应以 label 为准。
2. 阈值 j>B平方为简称，与 tex 实际阈值（9B平方/4；max(B,|C|)平方）不完全一致，已按 tex 为准记录。
3. paper1 正文（第803-824行）关于 Perron、Stambul、Hetyei 只处理定性 Hurwitzian 闭包、不跟踪 quasi-period 长度的论述，与本次打开的 Stambul 全文、Hetyei 第1.2节原文一致；但正文同时声称的 Komatsu 系列无先例细节超出本轮范围，未复核。

## 无法核实项

1. Perron (1954) Bd.1 第33节节内 Satz 编号、第33节是否含有任何定量周期或阈值界。原书未取得；Hetyei 的沉默论断是二手证据，不能替代原文核对。卡在：DNB 三次不可达加无其他开放扫描。
2. Stambul 参考文献 [10]（1994 博士论文）是否含定量周期。本次未检索（超出 backlog 范围，主会话决定是否追查）。
3. DNB 关于第33节起始于 p.119 的声称。本次仍未打开 DNB 页，维持未核到（不否定原记录）。

## 它没有做到的事

1. 未取得 Perron 原书，节内 Satz 编号维持未核到。2. 只处理 2B平方、2B|C|、阈值三处定量陈述的新颖边界，不验证定理证明正确性，不对 e+pi 无理性构成任何推进（本轮纯属第 5 类文献核查）。3. 负搜索是关键词加各源 top-10 有限覆盖，报告无先例时已声明覆盖范围，不等于证明不存在先例。
