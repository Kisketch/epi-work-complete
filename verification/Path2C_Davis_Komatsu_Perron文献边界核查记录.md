# Path 2C：Davis–Komatsu–Perron–HBCM 文献边界核查记录

> **一句总判断**：经对 CrossRef 元数据、OpenAlex 公开索引、arXiv TeX 源码及 OA 期刊全文的逐篇核验，已精准界定 C.~S.~Davis (1945/1978)、R.~F.~C.~Walters (1968)、Takao Komatsu 系列论文 (1999–2026)、Havens–Barbero–Cerruti–Murru (2020) 与 Oskar Perron (1954, Band I, §33) 对仿射连分数窗口理论的覆盖边界（属**第 5 类：文献核查与复现**）；上述核查仅收紧论文一 `thm:affine-window` 与 `cor:affine-single` 的先行文献边界，**不声称亦不构成对 $e+\pi$ 无理性公开问题的推进**。

---

## 0. 诚实五分类对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| C.~S.~Davis (1945) & (1978) 与 R.~F.~C.~Walters (1968) 核查 | **5. 文献核查与复现** | **部分全文核实 / 1945 原文精确定理号「未核到」** | 仅处理 $e^{1/t}, e^{2/t}$ 主对角 Padé 逼近及正则连分数显式渐近分数，不覆盖一般非齐次仿射平移 $(A+Ce)/B$ 或 5-窗锐性 | CrossRef (`10.1112/jlms/s1-20.4.194`, `10.1017/S1446788700021480`, `10.1017/S1446788700005255`)；Davis (1978) pp. 497–502；Walters (1968) pp. 205–212 |
| Takao Komatsu 系列 (1999–2026) 核查 | **5. 文献核查与复现** | **5 篇 OA 全文已读 / 付费期刊文具体定理号「未核到」** | 集中于 $e^{1/s}, e^{2/s}$ 与 Tasoev 连分数之 ${}_0F_1$ 超几何闭式、跳跃渐近分数、非齐次常数 $M(\theta,\phi)$ 及非正则 $N$-连分数（2009 摘要）；在已检索范围内负搜索未见 $(A+Ce)/B$ 窗长判据与 5-窗锐性 | OpenAlex 38 条记录；5 篇 OA 全文（1999 JTNB, 2003 Tsukuba, 2007 Czech, 2008 Sarajevo, `arXiv:2604.09726`）；2003/2005/2009 付费文 DOI 及摘要核验 |
| Havens–Barbero–Cerruti–Murru (2020) 核查 | **5. 文献核查与复现** | **已核实**（CrossRef + arXiv 全文） | 全文解决 $|\det\sigma|=2$ 线性分式变换与非线性跳跃递推，第 2 页明言 $|\det\sigma|>2$ 时一般规律极难处理；直接佐证一般 $(A+Ce)/B$（$|\det|=BC$ 任意大）无现成覆盖 | *Res. Number Theory* **6** (2020), art. 11 (`doi:10.1007/s40993-020-0187-5`, `arXiv:2002.12644` L105–116) |
| Oskar Perron (1954, Band I, §33) 边界核查 | **5. 文献核查与复现** | **第三方一手全文转述已核实 / 原书精确页码与 Satz 编号「未核到」** | 据 Hetyei (2014, §1.2, p. 4) 原文引述，Perron §33 保持 Hurwitzian 性并控制多项式次数，但对变换后准周期长度的变化“保持沉默” | Hetyei (`arXiv:1211.2494v2`, L285–294, L1877–1880)；DNB 元数据（1954 第 3 版 Band I） |
| 负搜索边界声明（2018–2026 及公开数据库） | **5. 文献核查与复现（负搜索）** | **负搜索未找到先例** | 检索覆盖 CrossRef、OpenAlex（截至 2026-11）、arXiv（至 `2604.09726`）、Numdam、DML-CZ 与 Cambridge OA，未见 $(A+Ce)/B$ 窗长判据 $r_j=1\iff G_jG_{j+1}=T$ 及 5-窗锐性先例 | **仅声明负搜索未见先例，不宣称已证明不存在先例** |

---

## 1. 逐篇核查台账与书目补正

### 1.1 C. S. Davis (1945, 1978) 与 R. F. C. Walters (1968)
- **Davis (1945)**：C.~S.~Davis, *On some simple continued fractions connected with $e$*, J. London Math. Soc. **s1-20** (1945), no. 4, 194–198, `doi:10.1112/jlms/s1-20.4.194`（CrossRef API 核对）。
  - **未核到字段**：1945 年原文 PDF 位于 Wiley 付费墙内未打开，故该文**精确定理编号**严格标记为「**未核到**」。
  - **内容边界**：结合 Davis (1978) 及 Walters (1968) OA 全文交叉确认，Davis (1945) 处理 $e^{1/t}$、$e^{2/t}$（$t\in\N$）的正则连分数与主对角 Padé 逼近渐近分数，不涉及一般非齐次仿射平移 $(A+Ce)/B$、Hermite 截断窗口长度 $r_j$ 判定或 5-窗锐性刻画。
- **Davis (1978)**：C.~S.~Davis, *Rational approximations to $e$*, J. Austral. Math. Soc. **25** (1978), no. 4, **497–502**, `doi:10.1017/S1446788700021480`（Cambridge OA 全文核对；修正前稿一度将页码误记为 `497–498`，实为导言提及 1945 文所在起止页，全篇页码为 `497–502`）。
- **Walters (1968)**：R.~F.~C.~Walters, *Alternative derivation of some regular continued fractions*, J. Austral. Math. Soc. **8** (1968), 205–212, `doi:10.1017/S1446788700005255`（Cambridge OA 全文核对）。

### 1.2 Takao Komatsu 系列（1996–2026）
- **已打开全文核对的 5 篇 OA 文献**：
  1. T.~Komatsu, *On inhomogeneous Diophantine approximation with some quasi-periodic expressions, II*, J. Théor. Nombres Bordeaux **11** (1999), no. 2, 331–344, `doi:10.5802/jtnb.254`（Numdam PDF 已读）。
  2. T.~Komatsu, *Simple continued fraction expansions of some values of certain hypergeometric functions*, Tsukuba J. Math. **27** (2003), no. 1, 161–173, `doi:10.21099/tkbjm/1496164567`（Tsukuba PDF 已读）。
  3. T.~Komatsu, *Hurwitz continued fractions with confluent hypergeometric functions*, Czechoslovak Math. J. **57 (132)** (2007), no. 3, 919–932, `doi:10.1007/s10587-007-0085-1`（DML-CZ PDF 已读）。
  4. T.~Komatsu, *More on Hurwitz and Tasoev continued fractions*, Sarajevo J. Math. **4 (17)** (2008), no. 2, 155–180, `doi:10.5644/sjm.04.2.02`（SJM PDF 已读；注：CrossRef `issued` 字段因追补 DOI 误标 `2024-06-11`，期刊卷期年份为 2008）。
  5. N.~Kalinin and T.~Komatsu, *Error terms for continued fractions of $e^{1/s}$ and $\sqrt{v/u}\tanh(1/\sqrt{uv})$*, `arXiv:2604.09726` (2026)（arXiv TeX 源码已读；研究 $e^{1/s}$ 与 $\sqrt{v/u}\tanh(1/\sqrt{uv})$ 误差项阶乘级数与组合恒等式，未涉 $(A+Ce)/B$ 窗口理论）。
- **已核对 DOI / 元数据但未取得付费全文的文献**（精确定理编号严格标记为「**未核到**」）：
  - *Acta Arith.* **107** (2003), 161–177, `doi:10.4064/aa107-2-4`；
  - *Monatsh. Math.* **145** (2005), 47–60, `doi:10.1007/s00605-004-0281-0`；
  - *J. Number Theory* **129** (2009), 358–366, `doi:10.1016/j.jnt.2008.08.004`（据出版商公开摘要核实：其“将周期缩减至 1”是将拟周期简单连分数转化为**非正则 / $N$-连分数**，与论文一 `cor:affine-single` 刻画的**正则简单连分数 Hermite 截断单字窗口 $r_j=1$** 完全不同）。
- **总体边界**：在 OpenAlex 检索的 38 条 Komatsu 连分数记录及已读 5 篇全文中，研究集中在超几何函数 ${}_0F_1$ 闭式、Tasoev/Hurwitz 连分数的跳跃渐近分数（leaping convergents）、非齐次逼近常数 $M(\theta,\phi)$（NST 算法）及 $N$-连分数；负搜索未见关于 $(A+Ce)/B$ 的 Hermite 截断窗口长度判据 $r_j=1\iff G_jG_{j+1}=T$ 或 5-窗锐性的先例。

### 1.3 Havens–Barbero–Cerruti–Murru (2020)
- **精确书目**：C.~Havens, S.~Barbero, U.~Cerruti, and N.~Murru, *Linear fractional transformations and nonlinear leaping convergents of some continued fractions*, Res. Number Theory **6** (2020), **art. 11**, `doi:10.1007/s40993-020-0187-5`, `arXiv:2002.12644`（CrossRef 核实 `article-number: 11`，arXiv TeX 源码 L105–116 直接核读）。
- **内容边界**：原文第 2 页明言，当变换矩阵行列式 $|\det\sigma|>2$ 时一般线性分式变换下的连分数规律远更困难、需另辟途径；全文仅处理 $|\det\sigma|=2$ 族与非线性跳跃递推。这直接印证一般仿射家族 $(A+Ce)/B$（行列式 $BC$ 任意大）并无现成定理覆盖。

### 1.4 Oskar Perron (1954, Band I, §33)
- **精确书目**：O.~Perron, *Die Lehre von den Kettenbrüchen*, 3. verb. u. erw. Aufl., Band I: *Elementare Kettenbrüche*, B.~G.~Teubner, Stuttgart, 1954（DNB 目录元数据核对；具体引文经 G.~Hetyei, *Hurwitzian continued fractions containing a repeated constant and an arithmetic progression*, SIAM J. Discrete Math. **28** (2014), no. 2, 962–985, `arXiv:1211.2494v2`, §1.2 p. 4, L285–294 与 L1877–1880 源码交叉核对）。
- **未核到字段**：1954 年 Band I 原书实体/扫描本未打开，故 §33 在 1954 版中的**原书精确页码与 Satz 编号**严格标为「**未核到**」。
- **内容边界**：Hetyei (2014, §1.2) 明确引述 Perron (1954, Band I, §33) 证明了有理 Möbius 变换保持 Hurwitzian 性并控制多项式次数，但对变换后准周期长度的变化“保持沉默”（`"remains silent however on the issue how the length of the period may be affected"`）。这与论文一 `thm:affine-window`（给出显式周期 $T=2B|C|$、窗长判据及 5-窗锐性）形成精准衔接。

---

## 2. 它没做到什么（范围与限制声明）
1. 付费墙与纸本原件限制：Davis (1945)、Perron (1954, Band I) 原书实体页码/Satz 编号、以及 Komatsu 部分付费期刊文（*Acta Arith.* 2003, *Monatsh. Math.* 2005, *JNT* 2009）全文未取得，所有未直接打开原件的细目均已严标「**未核到**」。
2. 负搜索不等于存在性证明：检索覆盖 CrossRef、OpenAlex（截至 2026-11）、arXiv（至 `2604.09726`）、Numdam、DML-CZ 与 Cambridge OA；结论严格限定为「负搜索未找到先例」，不排除非公开或未索引文献中的潜在局部重叠。
3. 本核查仅校准论文一 §8 中 `thm:affine-window` 与 `cor:affine-single` 的文献边界，不对 $e+\pi$ 无理性构成任何直接或间接推进。
