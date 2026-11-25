# E9｜KMS 相变对照资料（检索与抄录）

- 任务来源：`verification/flash_task_briefs_v2_20261124.md` E9（P2B「与 Kesseböhmer–Munday–Stratmann 热力学形式体系相变对照专节」素材页）。
- 执行日期：2026-11-24。工具：本环境 `web_search`（autoglm 提供方）+ `fetch_content` 实际打开页面。
- 范围声明：本文件**只检索与抄录**，不含对本论文（paper2）的任何评价性文字或比较判断。所有条目按 AGENTS.md §2 属类别 5「文献核查与复现」素材。
- 引用纪律（AGENTS.md §3）：书目字段**只来自本轮实际打开的页面**；未核到的字段一律写「未核到」。英文摘录为照录（保留原文拼写与记号，含源页面文本抽取可能产生的空格/连字差异）。
- 证据等级：**P·DOI**（题名/作者/年份/刊载/DOI 核自实际打开的出版方或 arXiv 官方页，含 DOI 字段）；**P·卷页**（卷期页核自实际打开的官方页但无 DOI 字段或 DOI 未核到）；**R·二手**（核自已打开的他文参考文献列表等二手源）；**未核到**。

## 一句总判断

核到 **6 篇 2010–2026 年论文 + 1 部 KMS 专著**（全部书目字段来自实际打开页面），另有 2 篇年限内补充条目与 4 条超年限背景条目；「capped-height」为**精确短语负搜索**（非"证明不存在"），详见第 4 节。

## 0. 总对照表（主条目）

| # | 结果 | 年份 | 刊载 | 证据等级 | URL |
|---|------|------|------|----------|-----|
| M1 | Kesseböhmer & Stratmann, sum-level sets 的 Lebesgue 测度渐近 | 2012 | DCDS-A 32(7): 2437–2451, DOI 10.3934/dcds.2012.32.2437 | P·DOI | [arXiv:0901.1787](https://arxiv.org/abs/0901.1787) |
| M2 | Kesseböhmer–Munday–Stratmann, α-Farey/α-Lüroth 强更新定理与 Lyapunov 谱 | 2012 | Ergodic Theory Dynam. Systems 32(3): 989–1017, DOI 10.1017/S0143385711000186 | P·DOI | [arXiv:1006.5693](https://arxiv.org/abs/1006.5693) |
| M3 | Bonanno, Farey 图广义转移算子 | 2023（2022-12-27 上线） | Mathematics 11(1): 134（文章号）, DOI 10.3390/math11010134 | P·DOI | [MDPI](https://www.mdpi.com/2227-7390/11/1/134) |
| M4 | Dodds, Farey 图热力学形式（相变 β=1） | 2017（arXiv 存档；论文正文为 1994 硕士论文） | 刊载：未核到（arXiv 存档，无期刊出处） | P·DOI（存档级） | [arXiv:1701.04486](https://arxiv.org/abs/1701.04486) |
| M5 | Jordan & Rams, weak Gibbs 测度多重分形分析 | 2011 | Ergodic Theory Dynam. Systems 31(1): 143–164（卷页 R·二手） | P·DOI（预印本）+ R | [arXiv:0806.0727](https://arxiv.org/abs/0806.0727) |
| M6 | Rapaport, 独立数字连分数的维数间隔 | 2018 | Israel J. Math. 227(2): 911–930, DOI 10.1007/s11856-018-1753-6 | P·DOI + P·卷页 | [arXiv:1703.03164](https://arxiv.org/abs/1703.03164) / [Technion CRIS](https://cris.technion.ac.il/en/publications/a-dimension-gap-for-continued-fractions-with-independent-digits-t) |
| B7（专著） | Kesseböhmer–Munday–Stratmann《Infinite Ergodic Theory of Numbers》 | 2016 | De Gruyter Textbook, Berlin/Boston, DOI 10.1515/9783110439427 | P·DOI | [De Gruyter](https://www.degruyterbrill.com/document/doi/10.1515/9783110439427/html) |

---

## 1. 主条目（2010–2026 论文，6 篇）

### M1｜Kesseböhmer & Stratmann（2012）— sum-level sets 与热力学意义

- **题名**：On the Lebesgue measure of sum-level sets for continued fractions（arXiv 版）；期刊版题名：On the asymptotic behaviour of the Lebesgue measure of sum-level sets for continued fractions
  - 说明：期刊版题名多出 "asymptotic behaviour"，核自 Bernd O. Stratmann 官方出版物页（打开的 http://www.math.uni-bremen.de/bos/publications.html ，R·二手）；arXiv 页 journal-ref 未含题名。
- **作者**：Marc Kesseböhmer, Bernd O. Stratmann（arXiv 页）
- **年份**：2012（期刊出版年；arXiv v1 2009-01-13）
- **刊载**：Discrete and Continuous Dynamical Systems. Series A 32 (2012), no. 7, 2437–2451（arXiv 页 Journal reference 字段）
- **DOI**：10.3934/dcds.2012.32.2437（arXiv 页 Related DOI 字段）
- **URL**：https://arxiv.org/abs/0901.1787 ；出版方文章页 http://www.aimsciences.org/article/doi/10.3934/dcds.2012.32.2437 （已打开；抓取仅返回其参考文献段，题名/摘要字段未在该次抓取中出现，故书目以 arXiv journal-ref + Uni-Bremen 页为准）
- **相变/临界结论英文摘录（照录自 arXiv 页 Abstract）**：
  > "The first main result is to settle a recent conjecture of Fiala and Kleban, which asserts that the Lebesgue measure of these level sets decays to zero, for the level tending to infinity. The second and third main result then give precise asymptotic estimates for this decay. … The paper closes with a discussion of the thermodynamical significance of the obtained results, and with some applications of these to metrical Diophantine analysis."
  - （注：省略号处为摘录中间句，非原文删除；全文见所开页面。）
- **证据等级**：P·DOI（journal-ref/DOI 来自打开的 arXiv 官方页）
- **主题归类**：K–S 系；sum-level 测度渐近（临界/无限测度统计性质）；文中引 Prellberg–Slawny（见其参考文献 [23]，已打开的 aimsciences 页）。

### M2｜Kesseböhmer, Munday & Stratmann（2012）— α-Farey/α-Lüroth 的 Lyapunov 谱与热力学形式

- **题名**：Strong renewal theorems and Lyapunov spectra for α-Farey and α-Lüroth systems
- **作者**：Marc Kesseböhmer, Sara Munday, Bernd O. Stratmann（arXiv 页）
- **年份**：2012（期刊出版年；arXiv v1 2010-06-29）
- **刊载**：Ergodic Theory Dynamical Systems 32 no. 3 (2012) 989–1017（arXiv 页 Journal reference 字段）
- **DOI**：10.1017/S0143385711000186（arXiv 页 Related DOI 字段；Stratmann 官方页一致）
- **URL**：https://arxiv.org/abs/1006.5693
- **相变/临界结论英文摘录（照录自 arXiv 页 Abstract）**：
  > "The second remaining result is to obtain a complete description of the Lyapunov spectra of the $\alpha$-Farey map and the $\alpha$-Lüroth map in terms of the thermodynamical formalism. We show how to derive these spectra, and then give various examples which demonstrate the diversity of their behaviours in dependence on the chosen partition $\alpha$."
- **证据等级**：P·DOI
- **主题归类**：KMS 三人合著；Farey/Gauss 图线性化推广系统的热力学形式描述；维数/Lyapunov 谱。

### M3｜Bonanno（2023，2022-12-27 上线）— Farey 图广义转移算子（温度参数与相变综述位置）

- **题名**：On the Generalised Transfer Operators of the Farey Map
- **作者**：Claudio Bonanno（MDPI 特刊页与期刊卷页列表署名单作者；文章页头部未被本次抓取捕获，作者信息以 MDPI 特刊官方页为准）
- **年份**：2023（卷期年）；Published 27 December 2022（MDPI 特刊页）
- **刊载**：*Mathematics* 2023, 11(1), 134（文章号 134）；Special Issue "Advances in Ergodic Theory and Its Applications"（MDPI 特刊页照录：`Mathematics 2023, 11(1), 134; https://doi.org/10.3390/math11010134 - 27 Dec 2022`）
- **DOI**：10.3390/math11010134
- **URL**：https://www.mdpi.com/2227-7390/11/1/134 （全文已打开）+ https://www.mdpi.com/journal/mathematics/special_issues/Adv_Ergod_Theory_Appl （已打开，引文行照录）
- **相变/临界结论英文摘录（照录自文章 §1 Introduction，已打开全文）**：
  > "When considering non-uniformly hyperbolic systems, one expects to obtain a statistical mechanics system with slow convergence toward equilibrium and a phase transition to appear. This phenomenon has been studied accurately for the Farey map in [7,8]."
  - 其中 [7] = Prellberg, T. "Towards a complete determination of the spectrum of a transfer operator associated with intermittency." J. Phys. A **2003**, 36, 2455–2461；[8] = Prellberg, T.; Slawny, J. "Maps of intervals with indifferent fixed points: Thermodynamic formalism and phase transitions." J. Statist. Phys. **1992**, 66, 503–514（两条核自该文参考文献列表，已打开，R·二手）。
  - 另一可选摘录（同文 §1）：> "In particular, it turns out that it is interesting to find the values of the temperature for which the transfer operator has 1 as the eigenvalue with the eigenfunction of a given type."
- **证据等级**：P·DOI
- **主题归类**：Farey 图转移算子族（实/复温度）；相变综述位置；与 modular surface 谱理论连接。

### M4｜Dodds（arXiv 2017）— Farey 图热力学形式与 β=1 相变

- **题名**：On the Thermodynamic Formalism for the Farey Map
- **作者**：Peter Sheridan Dodds（arXiv 页）
- **年份**：arXiv 提交 2017-01-16；**论文正文为 1994 年墨尔本大学硕士论文（1995 年授学位）**——照录 arXiv Comments 字段："100 pages, 10 figures, Masters Thesis created at the University of Melbourne, Australia, 1994; degree awarded 1995"
- **刊载**：**未核到**（无期刊出处，arXiv 存档；非同行评审期刊论文，主会话引用时请注意其性质）
- **DOI**：10.48550/arXiv.1701.04486（arXiv-issued DOI，DataCite）
- **URL**：https://arxiv.org/abs/1701.04486
- **相变/临界结论英文摘录（照录自 arXiv 页 Abstract）**：
  > "In particular, the asymptotic behaviour of the pressure function in the limit $\beta$, the inverse of `temperature', tends to negative infinity is determined and the existence and nature of a phase transition at $\beta=1$ is also discussed."
- **证据等级**：P·DOI（arXiv 存档级；刊载未核到）
- **主题归类**：Farey 图压力函数渐近与 β=1 相变的显式陈述（该结果谱系另见背景条目 BG2/BG3）。

### M5｜Jordan & Rams（2011）— weak Gibbs 测度的多重分形分析

- **题名**：Multifractal analysis of weak Gibbs measures for non-uniformly expanding C^1 maps
- **作者**：Thomas Jordan, Michal Rams（arXiv 页）
- **年份**：2011（期刊出版年；arXiv v1 2008-06-04）
- **刊载**：Ergodic Theory Dynam. Systems 31 (2011), no. 1, 143–164 —— 卷页核自已打开的 Iommi–Yayama 论文（作者版 PDF，PAMS 2017 刊印稿）参考文献行："[JR] T. Jordan and M. Rams Multifractal analysis of weak Gibbs measures for non-uniformly expanding C1 maps. Ergodic Theory Dynam. Systems 31 (2011), no. 1, 143–164."；**arXiv 页无 Journal reference 字段**；ADS/numdam/semanticscholar 检索摘要一致（未逐一打开）。
- **DOI**：**未核到**（未打开 Cambridge 页）
- **URL**：https://arxiv.org/abs/0806.0727
- **相变/临界结论英文摘录（照录自 arXiv 页 Abstract）**：
  > "We consider the local dimension spectrum of a weak Gibbs measure on a C^1 non-uniformly hyperbolic system of Manneville- Pomeau type. We present the spectrum in three ways: using invariant measures, uniformly hyperbolic ergodic measures and equilibrium states."
  - （注："Manneville- Pomeau" 中的空格为源页面文本抽取原样；Manneville–Pomeau 型即含 indifferent fixed point 的间歇映射，Farey 型。）
- **证据等级**：P·DOI（预印本页）+ 刊载卷页 R·二手；DOI 未核到
- **主题归类**：weak Gibbs 主题主条目；C¹ 非一致扩张（间歇型）系统的局部维数谱。

### M6｜Rapaport（2018）— 独立数字连分数的维数间隔

- **题名**：A dimension gap for continued fractions with independent digits---the non stationary case
- **作者**：Ariel Rapaport（Technion CRIS 页与 arXiv 提交记录一致）
- **年份**：2018
- **刊载**：Israel Journal of Mathematics 227 (2), 911–930（Technion CRIS 官方页照录：Pages 911–930, Volume 227, Issue number 2, Published - 2018）
- **DOI**：10.1007/s11856-018-1753-6（Technion CRIS 页）
- **URL**：https://cris.technion.ac.il/en/publications/a-dimension-gap-for-continued-fractions-with-independent-digits-t ；预印本 https://arxiv.org/abs/1703.03164
- **相变/临界结论英文摘录（照录自 arXiv 页 Abstract）**：
  > "We show there exists a constant $0<c_{0}<1$ such that the dimension of every measure on $[0,1]$, which makes the digits in the continued fraction expansion independent, is at most $1-c_{0}$. This extends a result of Kifer, Peres and Weiss from 2001, which established this under the additional assumption of stationarity."
- **证据等级**：P·DOI + P·卷页
- **主题归类**：Gauss 系统数字独立测度的维数上界（Kifer–Peres–Weiss 2001 谱系的非平稳推广）。

## 2. 专著（不计入论文计数）

### B7｜Kesseböhmer, Munday & Stratmann（2016）—《Infinite Ergodic Theory of Numbers》

- **题名**：Infinite Ergodic Theory of Numbers
- **作者**：Marc Kesseböhmer, Sara Munday, Bernd Otto Stratmann（De Gruyter 页 "Cite this book" 照录：`Kesseböhmer, Marc, Munday, Sara and Stratmann, Bernd Otto. Infinite Ergodic Theory of Numbers, Berlin, Boston: De Gruyter, 2016. https://doi.org/10.1515/9783110439427`）
- **年份**：2016（Published/Copyright: 2016；eBook 2016-10-10）
- **刊载**：De Gruyter Textbook 丛书，Berlin/Boston；eBook ISBN 9783110439427；Paperback ISBN 9783110439410；DOI 10.1515/9783110439427（均照录自 De Gruyter 页 Bibliographic data 段）
- **目录（照录）**：1. Number-theoretical dynamical systems；2. Basic ergodic theory；3. Renewal theory and α-sum-level sets；4. Infinite ergodic theory；5. Applications of infinite ergodic theory。
- **出版方书介英文摘录（照录自 De Gruyter 页 About this book）**：
  > "The text explores various concepts in infinite ergodic theory, always using continued fractions and other number-theoretic dynamical systems as illustrative examples."
- **相变/临界结论正文摘录**：**未核到**（正文页 Requires Authentication；本条摘录为出版方书介，非相变结论原句）
- **证据等级**：P·DOI
- **主题归类**：KMS 三人专著；Farey/Gauss 图与 α-sum-level 集的无限遍历论教材，为 P2B 对照专节的基础文献。

## 3. 补充条目（年限内、主题邻近；不计入主 6 篇）

### S8｜Iommi & Yayama（2017）— weak Gibbs 测度即渐近可加序列的 Gibbs 测度

- **题名**：Weak Gibbs measures as Gibbs measures for asymptotically additive sequences
- **作者**：Godofredo Iommi, Yuki Yayama（arXiv 页）
- **年份**：2017（期刊出版年；arXiv v1 2015-05-05）
- **刊载**：Proceedings of the AMS 145, no 4. 1599–1614 (2017)（照录 arXiv 页 Journal reference 字段）
- **DOI**：**未核到**（arXiv 页无 Related DOI 字段；未打开 AMS 文章页）
- **URL**：https://arxiv.org/abs/1505.00977
- **英文摘录（照录自 arXiv 页 Abstract）**：
  > "In this note we prove that every weak Gibbs measure for an asymptotically additive sequences is a Gibbs measure for another asymptotically additive sequence."
  - （注：原文摘要即如此，"sequences" 单复数照录。weak Gibbs 概念出处另见其正文与参考文献：Yuri 三文（BG4）。）
- **证据等级**：P·卷页（journal-ref 核自打开的 arXiv 页）+ P·DOI（预印本 DOI 10.48550/arXiv.1505.00977）；期刊 DOI 未核到
- **主题归类**：weak Gibbs 主题；文中引 Kesseböhmer 的 weak Gibbs 存在性结果（已打开作者版 PDF，mat.uc.cl）。

### S9｜Tang（arXiv 2025）— 奇/偶位有界偏商连分数集的 Hausdorff 维数（capped-height 最邻近）

- **题名**：Hausdorff dimension of sets of continued fractions with bounded odd and even order partial quotients
- **作者**：Yuefeng Tang（arXiv 页）
- **年份**：2025（arXiv 提交 2025-07-21）
- **刊载**：**未核到**（arXiv 页无 Journal reference 字段）；arXiv Comments 字段照录："This is the English version of the author's undergraduate thesis. Comments are welcome"——**非同行评审期刊论文**。
- **DOI**：10.48550/arXiv.2507.15552（arXiv-issued DOI）
- **URL**：https://arxiv.org/abs/2507.15552
- **英文摘录（照录自 arXiv 页 Abstract）**：
  > "We study the continued fractions with bounded odd/even-order partial quotients. In particular, we investigate the sizes of the sets of continued fractions whose odd-order partial quotients are equal to 1."
- **证据等级**：P·DOI（预印本存档级）；刊载未核到
- **主题归类**：任务书「capped-height」主题的最邻近文献（有界偏商型集合的维数）；精确术语负搜索说明见第 4 节。

## 4. 检索覆盖范围与负搜索说明（负搜索 ≠ 不存在）

**检索词族（本轮实际执行，web_search/autoglm 提供方）**：
1. Kesseböhmer Stratmann multifractal Stern-Brocot intervals continued fractions Diophantine growth rates
2. Farey map phase transition thermodynamic formalism continued fractions
3. capped height continued fractions Hausdorff dimension arxiv
4. Munday dimension gap continued fractions independent partial quotients
5. "capped height" continued fractions（精确短语）
6. Kesseböhmer Munday Stratmann "Strong renewal theorems and Lyapunov spectra" alpha-Farey alpha-Lüroth（带变音符，返回 0 条；去变音符改词后命中 arXiv:1006.5693）
7. "weak Gibbs" Gauss map continued fraction thermodynamic formalism phase transition（返回 0 条）
8. weakly Gibbs measures continued fractions Gauss map（返回 0 条）
9. Kesseböhmer Munday Stratmann "Infinite Ergodic Theory and Continued Fractions" book（实际书名为 Infinite Ergodic Theory of Numbers）
10. Kesseböhmer "Discrete and Continuous Dynamical Systems" 2012 32 2437 Farey Lebesgue measure asymptotic
11. arxiv weak Gibbs property Gauss map continued fraction invariant density
12. continued fractions bounded partial quotients thermodynamic formalism pressure arxiv
13. Rapaport "dimension gap" continued fractions independent digits Israel Journal
14. Jordan Rams "multifractal analysis of weak Gibbs measures" journal
15. "weak Gibbs" "Gauss map" OR "Farey" dynamical systems
16. "height of continued fractions" maximum partial quotient Hausdorff dimension arxiv 2015
17. "weakly Gibbs" measure dimension arxiv
18. Iommi Yayama "weak Gibbs measures" "asymptotically additive sequences" Proceedings AMS
19. "10.3390/math11010134" Bonanno Farey transfer operators
20. arxiv weak Gibbs（改词系列）

**负搜索结论（只是负搜索，不是证明不存在）**：
- **「capped-height」精确短语**：`"capped height" continued fractions` 与 capped-height 相关查询在本检索环境返回的均为工程/半导体领域同形词结果（桥梁堆芯、量子点外延、烟囱高度等），**未命中数学文献**。已改用「bounded partial quotients / bounded odd and even order partial quotients」词族，命中 S9（arXiv 预印本）。经典的有界偏商维数理论（如 Hensley 的相关工作）本轮未打开任何页面核对，书目字段**未核到**，不作引用。
- **weak Gibbs 初轮命中为 0**：词族 7、8 返回 0 条；改词（"weak Gibbs" "Gauss map" OR "Farey"）后命中 M5/S8 线索。weak Gibbs 文献覆盖可能不完整。
- **出版方页面**：Springer（IJM/Crelle/ETDS）与 AMS 文章页未直接打开；IJM 卷页经 Technion CRIS 官方页核对（P·卷页），ETDS 卷页经 arXiv journal-ref（M2 为 P·DOI；M5 仅 R·二手）。
- **aimsciences 页**：M1 出版方文章页已打开，但抓取仅返回参考文献段，题名/摘要字段未在该次抓取中出现（已如实标注）。
- 未使用 MathSciNet / ZbMATH（无登录访问）；未覆盖付费墙内全文。

## 5. 超年限背景条目（不计入 2010–2026 主条目；均本轮实际打开核对）

| # | 条目 | 刊载 | 证据等级 | 摘录（照录） |
|---|------|------|----------|--------------|
| BG1 | Kesseböhmer & Stratmann, *A multifractal analysis for Stern-Brocot intervals, continued fractions and Diophantine growth rates*（2007） | J. Reine Angew. Math. (Crelle) 605 (2007), 133–163, DOI 10.1515/CRELLE.2007.029（arXiv:math/0509603 页 Journal reference/Related DOI 字段；Uni-Bremen 页一致） | P·DOI | "In particular, we give detailed discussions of two multifractal spectra closely related to the Farey map and the Gauss map." |
| BG2 | Prellberg & Slawny, *Maps of intervals with indifferent fixed points: Thermodynamical formalism and phase transition*（1992） | J. Statist. Phys. 66 (1992), 503–514（核自已打开的 Bonanno 文章参考文献 [8] 与 aimsciences DCDS 2012 文章参考文献 [23]，两处一致；期刊页未打开） | R·二手 | 相变结论原句未核到（未打开期刊页） |
| BG3 | Prellberg, *Towards a complete determination of the spectrum of a transfer operator associated with intermittency*（2003） | J. Phys. A 36 (2003), 2455–2461（核自已打开的 Bonanno 文章参考文献 [7]） | R·二手 | 相变结论原句未核到（未打开期刊页） |
| BG4 | Yuri weak Gibbs 三文（2002/2002/2003） | [Y1] Comm. Math. Phys. 241 (2003), no. 2-3, 453–466；[Y2] Ergodic Theory Dynam. Systems 22 (2002), no. 6, 1933–1955；[Y3] Comm. Math. Phys. 230 (2002), no. 2, 365–388（核自已打开的 Iommi–Yayama 作者版 PDF 参考文献行） | R·二手 | weak Gibbs 概念出处；结论原句未核到（未打开期刊页） |

- BG1 说明：K–S 多重分形维数谱的直接前驱工作，期刊版 2007 年（早于 2010 下限），故列入背景；本轮 arXiv 页与 Uni-Bremen 页均已打开。
- BG2/BG3 说明：Bonanno 摘录中 "[7,8]" 即此二文；M4（Dodds 1994 论文）系同一谱系的独立陈述。indifferent fixed point（中性不动点）为 Farey/Gauss 相变的经典机制。
- BG4 说明：weak Gibbs 概念的文献出处（Yuri，间歇系统平衡测度研究），Iommi–Yayama 正文照录："In her study of equilibrium measures for intermittent interval maps, Yuri [Y1, Y2, Y3] introduced the notion of weak Gibbs measure."（该句核自作者版 PDF 文本抽取，连字符换行处空格已复原，原文以链接页为准。）

## 6. 未核到字段汇总

- M4（Dodds）：期刊刊载未核到（arXiv 存档，无期刊出处）。
- M5（Jordan–Rams）：DOI 未核到；卷页为 R·二手（arXiv 无 journal-ref）。
- S8（Iommi–Yayama）：期刊 DOI 未核到。
- S9（Tang）：期刊刊载未核到（预印本 + 本科论文版本）。
- B7（KMS 专著）：相变/临界结论正文摘录未核到（正文需认证登录）。
- BG2、BG3、BG4：相变/结论原句未核到（仅经二手参考文献核对书目）。
- Hensley 有界偏商经典工作：完全未核到（未打开任何页面）。

—— 检索与抄录至此为止；不含对本论文的评价。素材供主会话撰写 P2B 对照专节时直接取用。
