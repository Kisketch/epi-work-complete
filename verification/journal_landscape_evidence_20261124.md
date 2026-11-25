# E5 期刊版图——核验台账（2026-11-24）

> 本文件是 `verification/journal_landscape_20261124.md` 的核验底稿：逐条记录**实际打开过的页面 URL** 及页面上**实际出现的字段**。凡未在已打开页面上出现的字段，一律记「未核到」。
> 检索日期：2026-11-24。工具：`web_search`（仅作线索）+ `fetch_content`（实际打开页面）。
> 级别标注：**P** = 出版社/文摘站原页（arXiv 摘要页计 P-arXiv，其中 journal-ref/Related DOI 为作者填报）；**A** = 作者/机构自编目录页（二手）；**R** = 他文页面的参考文献或 Crossref 引文列表（二手，通常无 DOI）。

## 0. 抓取通道测试结果（如实记录）

| 通道 | 结果 |
|---|---|
| `api.crossref.org`（JSON / BibTeX 变换）、`api.openalex.org`、`export.arxiv.org/api`、`citation-needed.springer.com`、`dblp.org`、`search.crossref.org` | `fetch_content_invalid_response` 或只返回页面外壳，**不可用** |
| `zbmath.org`、`projecteuclid.org`、`sciencedirect.com`、`arxiv.org/a/<作者>` | 打不开，**不可用** |
| `pubmed.ncbi.nlm.nih.gov` 检索页 | 返回「No results were found」，不可用于发现；单条记录页未试 |
| `link.springer.com` 期目录页 / `doi.org`→IOP、→Cambridge Core / arXiv `abs` 页 / CRAS（Mathdoc）/ AIMS 文章页 | 可读 |

结论：出版社覆盖不完整。**ScienceDirect（Adv. Math.、JMAA 等）、Project Euclid（Duke、Proc. AMS 旧卷、Real Analysis Exchange 等）的落地页本次无法打开**，相关条目只能靠 arXiv 摘要页（作者填报 DOI）或作者目录页转证，已逐条标明。

## 1. 已打开页面台账

### P 类（出版社 / 文摘站原页）

| # | 页面 URL | 页面实际出现的字段 |
|---|---|---|
| P1 | https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.5802/crmath.699 | Mumtaz Hussain; Rebecca Smith; Zhenliang Zhang. *Fractional dimension of some exceptional sets in continued fractions*. Comptes Rendus. Mathématique, Volume 363 (2025), pp. 57-68. doi: 10.5802/crmath.699。Publié le 2025-03-06；MSC 11K55, 28A80 |
| P2 | https://doi.org/10.1088/1361-6544/ad140f （IOPscience） | Bo Tan and Qing-Long Zhou. *Metrical properties of the large products of partial quotients in continued fractions*. Nonlinearity, Volume 37, Number 2, 025008. DOI 10.1088/1361-6544/ad140f。Published 4 January 2024 |
| P3 | https://doi.org/10.1017/etds.2019.41 （Cambridge Core） | Ayreena Bakhtawar, Philip Bos, Mumtaz Hussain. *The sets of Dirichlet non-improvable numbers versus well-approximable numbers*. Ergodic Theory and Dynamical Systems, Volume 40, Issue 12, December 2020, pp. 3217 - 3235. DOI: 10.1017/etds.2019.41 |
| P4 | https://arxiv.org/abs/2104.15133 | Amlan Banaji, Jonathan M. Fraser. *Intermediate dimensions of infinitely generated attractors*. Journal reference: Trans. Amer. Math. Soc. 376 (2023) 2449-2479. Related DOI: https://doi.org/10.1090/tran/8766 |
| P5 | https://arxiv.org/abs/2207.11611 | Amlan Banaji, Jonathan M. Fraser. *Assouad type dimensions of infinitely generated self-conformal sets*. Journal reference: Nonlinearity 37 (2024), 045004. Related DOI: https://doi.org/10.1088/1361-6544/ad2864 |
| P6 | https://arxiv.org/abs/2111.05625 | Amlan Banaji, István Kolossváry. *Intermediate dimensions of Bedford-McMullen carpets with applications to Lipschitz equivalence*. Journal reference: Adv. Math. 449 (2024) 109735. Related DOI: https://doi.org/10.1016/j.aim.2024.109735 |
| P7 | https://arxiv.org/abs/2107.02616 | Marc Kesseböhmer, Aljoscha Niemann. *Spectral asymptotics of Krein--Feller operators for weak Gibbs measures on self-conformal fractals with overlaps*. Journal reference: Adv. Math. 403 (2022), Paper No. 108384, 33 pp. Related DOI: https://doi.org/10.1016/j.aim.2022.108384 |
| P8 | https://arxiv.org/abs/1905.09077 | Maik Gröger, Johannes Jaerisch, Marc Kesseböhmer. *Thermodynamic formalism for transient dynamics on the real line*. Journal reference: Nonlinearity 35, pp. 1093-1118, 2022. Related DOI: https://doi.org/10.1088/1361-6544/ac45ea |
| P9 | https://arxiv.org/abs/2007.15320 | De-Jun Feng, Károly Simon. *Dimension estimates for $C^1$ iterated function systems and repellers. Part I*。仅题名/作者；页面**无** journal-ref、**无** DOI |
| P10 | https://arxiv.org/abs/2106.14393 | De-Jun Feng, Károly Simon. *… Part II*。Comments: "Minor changes. To appear in Ergodic Theory Dynam. Systems"；**无**卷页、**无** DOI |
| P11 | https://arxiv.org/abs/1610.05827 | Johannes Jaerisch, Marc Kesseböhmer, Sara Munday. *A multifractal analysis for cuspidal windings on hyperbolic surfaces*。仅题名/作者；**无** journal-ref、**无** DOI |
| P12 | https://arxiv.org/abs/2307.07375 | Kevin G. Hare, Tomáš Vávra. *Self-similar sets and self-similar measures in the $p$-adics*。仅题名/作者；**无** journal-ref、**无** DOI |
| P13 | https://ems.press/journals/jfg/articles/14298107 | 仅抽出摘要正文；**题名/作者/卷页/DOI 均未在抽出文本中出现** |
| P14 | https://www.aimsciences.org/article/doi/10.3934/dcds.2024179 | 仅抽出摘要与参考文献；本条自身题名/作者/卷期未在抽出文本中出现；DOI 仅见于 URL：10.3934/dcds.2024179 |
| P15 | https://link.springer.com/journal/222/volumes-and-issues/243-3 | Inventiones mathematicae, Volume 243, Issue 3 (March 2026)：含 *Correction to: The Hausdorff and dynamical dimensions of self-affine sponges: a dimension gap result*，Tushar Das, David Simmons，Pages 1141 - 1142（勘误；原文为 2017 年，超出 2020–2026 代表作范围） |

### A 类（作者 / 机构自编目录页，二手）

| # | 页面 URL | 页面实际出现的字段 |
|---|---|---|
| A1 | https://www.math.cuhk.edu.hk/~djfeng/djfeng1.html （冯德俊论文目录） | Feng: *Dimension of invariant measures for affine iterated function systems*, Duke Math. J. 172 (2023), no. 4, 701--774；Feng & Simon: *Dimension estimates for $C^1$ iterated function systems and repellers. Part I*, Ergodic theory Dynam. Systems 43(2023), 2673--2706；*Part II*, Ergodic theory Dynam. Systems 42 (2022), no. 11, 3357--3392；Feng, Lo, Ma: *Dimensions of projected sets and measures on typical self-affine sets*, Adv. Math. 431(2023), Paper No. 109237；Feng & Feng: *Estimates on the dimension of self-similar measures with overlaps*, J. Lond. Math. Soc. 105 (2022), no. 4, 2104--2135；Feng: *On the Hausdorff Dimension of Bernoulli Convolutions*, Int. Math. Res. Not. IMRN 2020, no. 19, 6569--6595；Barral & Feng: *On multifractal formalism for self-similar measures with overlaps*, Math. Z. 298 (2021), no. 1-2, 359--383 |
| A2 | https://amlan-banaji.github.io/publications | Banaji & Kolossváry, Adv. Math. 449 (2024), 109735；Banaji & Fraser, Nonlinearity 37 (2024), 045004；Banaji, *Generalised intermediate dimensions*, Monatshefte für Mathematik 202 (2023), 465–506；Banaji & Fraser, Trans. AMS 376 (2023), 2449–2479；Banaji & Chen, *Dimensions of popcorn-like pyramid sets*, Journal of Fractal Geometry 10 (2023), 151–168；Banaji & Rutar, *Attainable forms of intermediate dimensions*, Annales Fennici Mathematici 47 (2022), 939–960 |
| A3 | https://www.uni-bremen.de/dynamical-systems/publications （Bremen 动力系统组论文目录） | Jaerisch, Kesseböhmer, Munday, *A multifractal analysis for cuspidal windings on hyperbolic surfaces*, Stochastics and Dynamics Vol. 21, No. 03, 2140007 (2021)；Gröger, Jaerisch, Kesseböhmer, *Thermodynamic formalism for transient dynamics on the real line*, Nonlinearity 35, 1093–1118 (2022)；Denker, Kesseböhmer, Lopes, Lopes, *Parametrized Families of Gibbs Measures and their Statistical Inference*, Stochastics and Dynamics, Vol. 25 No. 02, 2550012 (2025)；Kesseböhmer, Niemann, Zhu, *Quantization dimensions of compactly supported probability measures via Rényi dimensions*, Trans. Amer. Math. Soc. 376 (2023), pp. 4661-4678；Kesseböhmer, Samuel, Sender, *The Sierpiński gasket as the Martin boundary of a non-isotropic Markov chain*, J. Fractal Geom. 7: 113–136 (2020)；Kesseböhmer, Niemann, *Spectral dimensions of Krein-Feller operators and Lq-spectra*, Adv. Math. 399 (2022), Paper No. 108253 |
| A4 | https://leanprover-community.github.io/papers.html （Lean 社区论文目录） | Lewis & Wu, *A bi-directional extensible interface between Lean and Mathematica*, Journal of Automated Reasoning, 2022；Baanen, Dahmen, Narayanan, Nuccio Mortarino Majno di Capriglio, *A formalization of Dedekind domains and class groups of global fields*, J. Automat. Reason., 2022；Browning & Lutz, *Formalizing Galois Theory*, Experimental Mathematics, 2022；Buzzard, Hughes, Lau, Livingston, Mir, Morrison, *Schemes in Lean*, Exp. Math., 2022；Asgeirsson, Brasca, Kuhn, Nuccio Mortarino Majno di Capriglio, Topaz, *Categorical foundations of formalized condensed mathematics*, The Journal of Symbolic Logic, 2024；Marion, *A Formalization of the Ionescu-Tulcea Theorem in Mathlib*, Journal of Automated Reasoning, 2026；Loeffler & Stoll, *Formalizing zeta and L-functions in Lean*, Annals of Formalized Mathematics, 2025；Mercuri, *Formalising the local compactness of the adele ring*, Annals of Formalized Mathematics, 2025；Riou, *Formalization of derived categories in Lean/mathlib*, Annals of Formalized Mathematics, 2025；Ullrich & Moura, *'do' unchained: embracing local imperativity in a purely functional language (functional pearl)*, Proc. ACM Program. Lang., 2022；Selsam, Hudon, de Moura, *Sealing Pointer-Based Optimizations behind Pure Functions*, Proc. ACM Program. Lang., 2020；Wieser & Song, *Formalizing Geometric Algebra in Lean*, Advances in Applied Clifford Algebras, 2022 |

### R 类（他文页面的参考文献 / Crossref 引文列表，二手，均无 DOI）

| # | 页面 URL | 页面实际出现的字段 |
|---|---|---|
| R1 | 同 P3 页面下部 "Cited by"（页面注明 "generated based on data provided by Crossref"） | Li, Wang, Xu 2023, *Hausdorff dimension of Dirichlet non-improvable set versus well-approximable set*, Ergodic Theory and Dynamical Systems, Vol. 43, Issue. 8, p. 2707；Bakhtawar, Bos, Hussain 2020, *Hausdorff dimension of an exceptional set in the theory of continued fractions*, Nonlinearity, Vol. 33, Issue. 6, p. 2615；Feng, Xu 2021, *Sets of Dirichlet non-improvable numbers with certain order in the theory of continued fractions*, Nonlinearity, Vol. 34, Issue. 3, p. 1598；Hu, Hussain, Yu 2021, *Limit theorems for sums of products of consecutive partial quotients of continued fractions*, Nonlinearity, Vol. 34, Issue. 12, p. 8143；Kim, Kim 2022, *Hausdorff measure of sets of Dirichlet non-improvable affine forms*, Advances in Mathematics, Vol. 403, p. 108353；Ding, Feng 2025, *Hausdorff dimension of sets with large products of consecutive partial quotients and small single partial quotients in continued fractions*, Discrete and Continuous Dynamical Systems, Vol. 45, Issue. 8, p. 2650；Huang, Wu, Xu 2020, *Metric properties of the product of consecutive partial quotients in continued fractions*, Israel Journal of Mathematics, Vol. 238, Issue. 2, p. 901；Hussain, Shulga 2024, *Hausdorff dimension for sets of continued fractions of formal Laurent series*, Finite Fields and Their Applications, Vol. 95, p. 102377；Zhao, Zhang 2024, *Some lacunarity properties of partial quotients of real numbers*, Comptes Rendus. Mathématique, Vol. 362, Issue. G10, p. 1089；Wang, Li, Li 2024, *Uniform Diophantine approximation with restricted denominators*, Journal of Number Theory, Vol. 260, p. 232 |
| R2 | 同 P1 / P14 页面参考文献表 | Hussain, Li, Shulga, *Hausdorff dimension analysis of sets with the product of consecutive vs single partial quotients in continued fractions*, Discrete Contin. Dyn. Syst. 44 (2024) no. 1, pp. 154-181, doi: 10.3934/dcds.2023099（P14 页）；Huang, Wu, Xu, Israel J. Math. 238 (2020) no. 2, pp. 901-943, doi: 10.1007/s11856-020-2049-1（P14 页）；Bos, Hussain, Simmons, *The generalised Hausdorff measure of sets of Dirichlet non-improvable numbers*, Proc. Am. Math. Soc. 151 (2023) no. 5, pp. 1823-1838（P1 页）；Gayfulin, Shulga, *Diophantine properties of fixed points of Minkowski question mark function*, Acta Arith. 195 (2020) no. 4, pp. 367-382（P1 页） |

## 2. 已打开但不足以核到期刊字段的页面

| 页面 URL | 情况 |
|---|---|
| https://arxiv.org/abs/2209.08318 | Yuto Nakajima, Hiroki Takahasi, *Hausdorff dimension of sets with restricted, slowly growing partial quotients in semi-regular continued fractions*（v3 2024-07-17）；**无 journal-ref、无 DOI** → 是否已刊未核到，不作期刊论文收录 |
| https://arxiv.org/abs/1904.09812 | Michael Hochman, Ariel Rapaport, *Hausdorff Dimension of Planar Self-Affine Sets and Measures with Overlaps*；**无 journal-ref、无 DOI** → 刊载信息未核到（检索摘要称 JEMS 24(7)，未在已打开页面出现，**不采信**） |
| https://arxiv.org/abs/2507.15552 | Yuefeng Tang, *Hausdorff dimension of sets of continued fractions with bounded odd and even order partial quotients*；Comments 称为本科论文英文版；无 journal-ref → 不收录 |
| https://www.ams.org/proc/2021-149-10/S0002-9939-2021-15569-X | 抽出文本为一批他文的卷页/DOI 列表，**未出现** Evans 该文的题名/作者 → 该页不能用作核验 |
| https://www.urbanskimath.com/research/publications-and-preprints | 抽出部分仅含 2017 年及更早条目（无 2020–2026 条目）→ 未提供可用条目 |

| P16 | https://arxiv.org/abs/1901.01691 | De-Jun Feng. *Dimension of invariant measures for affine iterated function systems*（v2 2020-06-02）。**无** journal-ref、**无** DOI；刊载信息仅见 A1 |
| P17 | https://arxiv.org/abs/2205.15776 | Marc Kesseböhmer, Aljoscha Niemann, Sanguo Zhu. *Quantization dimensions of compactly supported probability measures via Rényi dimensions*. Journal reference: Trans. Amer. Math. Soc. 376 (2023), no. 7, 4661-4678. Related DOI: https://doi.org/10.1090/tran/8863 |
| P18 | https://arxiv.org/abs/2212.06961 | Amlan Banaji, Haipeng Chen. *Dimensions of popcorn-like pyramid sets*. Journal reference: J. Fractal Geom. 10 (2023) 151-168. Related DOI: https://doi.org/10.4171/JFG/135 |
| P19 | https://arxiv.org/abs/2010.14760 | Philip Bos, Mumtaz Hussain, David Simmons. *The generalised Hausdorff measure of sets of Dirichlet non-improvable numbers*. Comments: "In Press: Proceedings of the American Mathematical Society"；**无**卷页、**无** DOI（卷页仅见 R2） |

（P19 之前的编号见上表。）

### 抓取不全的页面

| 页面 URL | 情况 |
|---|---|
| https://arxiv.org/abs/2012.00177 | 抽出文本仅有摘要与 "From: James Evans"，**未出现**题名行与 journal-ref/DOI；题名 *The entropy and Hausdorff dimension of self-similar sets* 仅见于检索摘要 → 卷期/DOI 未核到 |

### 台账追加（第二批，写于成稿前）

| # | 页面 URL | 页面实际出现的字段 |
|---|---|---|
| P20 | https://arxiv.org/abs/1810.12599 | Kanji Inui, Hikaru Okada, Hiroki Sumi. *The Hausdorff dimension function of the family of conformal iterated function systems of generalized complex continued fractions*。Journal reference: "Published in Discrete Contin. Dyn. Syst. 40 (2020), no. 2, pp. 753--766"；**无** Related DOI |
| P21 | https://arxiv.org/abs/2011.08613 | Amlan Banaji. *Generalised intermediate dimensions*. Journal reference: Monatsh. Math. 202 (2023) 465-506. Related DOI: https://doi.org/10.1007/s00605-023-01884-5 |
| P22 | https://arxiv.org/abs/2408.01104 | Manfred Denker, Marc Keßeböhmer, Artur O. Lopes, Silvia R.C. Lopes. *Parametrized Families of Gibbs Measures and their Statistical Inference*（2024-08-02）。**无** journal-ref、**无** DOI（卷期仅见 A3） |
| P23 | https://arxiv.org/abs/2502.00772 | Nicolas E. Angelini, Ursula M. Molter, Jose M. Tejada. *Intermediate dimensions of measures: Interpolating between Hausdorff and Minkowski dimensions*（v2 2025-11-20）。Related DOI: https://doi.org/10.1016/j.jmaa.2025.130039；页面**未出现**期刊名与卷页 |
| P24 | https://doi.org/10.1088/1361-6544/acc71b （IOPscience；本次抓取前 20000 字为 cookie 声明，引文行取自同一页面的全文存档 `.zwork/runs/23e430a9/fetch_content-call_be77f0da107.md` 第 1050–1059 行） | Artem Dudko, Igors Gorbovickis and Warwick Tucker. *Lower bounds on the Hausdorff dimension of some Julia sets*. Nonlinearity, Volume 36, Number 5；"Artem Dudko et al 2023 Nonlinearity 36 2867"；DOI 10.1088/1361-6544/acc71b；Published 11 April 2023 |
| 抓取不全 | https://arxiv.org/abs/2304.06012 | 抽出文本仅有摘要与 "From: Vyron Vellis"；题名 *Parametrizability of infinitely generated attractors* 仅见于检索摘要；**无** journal-ref → 刊载信息未核到，不收录 |

### 仅见于检索结果、未打开页面的线索（不作已核字段）

- Zhao & Zhang, *Some lacunarity properties of partial quotients of real numbers*：CRAS 页 URL 末尾含 10.5802/crmath.594；检索摘要称 "Volume 362 (2024), p. 1089-1095"；卷期另见 R1。页面**未打开**。
- C. Matheus 等, *Hausdorff dimension of Gauss–Cantor sets and two …*, ScienceDirect PII S0001870822005102（2022，检索摘要）——**未打开**，题名不全。
- Rápaport, *Dimension of diagonal self-affine sets and measures via nonconformal partitions*, Wiley 10.1112/plms.70120（检索摘要称 Proc. Lond. Math. Soc. (3) 132 (2026), no. 1, e70120）——**未打开**。
- Hochman & Rapaport, JEMS 24(7):2361–2441（ResearchGate 检索摘要）——**未打开**，不采信。
- Denker, *General iterated function systems: Hausdorff dimension*, Chaos 2023 Mar;33(3):033118, doi 10.1063/5.0136663（PubMed 检索摘要）——**未打开**。
- Hare & Vávra, JFG 2024, 247–287, DOI 10.4171/JFG/154（检索摘要）——**未在已打开页面出现**，不采信。
- Okamura, Real Analysis Exchange 45(1) (2020), 10.14321/realanalexch.45.1.0029（Project Euclid，打不开）。
- Lean 论文 arXiv 编号（**未打开**，仅作 URL）：2102.02600（Baanen 等）、2101.02602（Buzzard 等）、2407.12840（Asgeirsson 等）、2405.19270（Mercuri）、2503.00959（Loeffler–Stoll）、2107.10988（Browning–Lutz）、2003.01685（Selsam 等）。Ullrich–de Moura 见 microsoft.com/en-us/research 出版页；Lewis–Wu 见 robertylewis.com/leanmm/lean_mm.pdf；Selsam 等 ACM DOI 10.1145/3408997（检索摘要）。

（台账到此为止；正式版图见 `verification/journal_landscape_20261124.md`。）
