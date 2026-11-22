# CMMS 引文一次文献核查记录（2026-11-22）

> 一句总判断：经直接打开核对本地预印本 `verification/reference_pdfs/h-sets.pdf` 与从官方 DOI 下载的正式刊出全文 `verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf`（*Pacific J. Math.* 217 (2004), No. 1, pp. 45–59），确认 Cabrelli–Mendivil–Molter–Shonkwiler 关于非增间隙序列 Cantor 集满足 $\frac{1}{32}\le\mathcal{H}^h(C_a)\le 1$ 的主定理编号在预印本与正式刊出本中**均为 §5, Theorem 3**（而非先前论文二所写的 Theorem 5）；论文二全篇三处引文已全部修正并重新双遍编译通过。

## 逐项对照表

| 结果 | 类别 | 核查状态 | 与已有文献关系 | 依据 |
| :--- | :--- | :--- | :--- | :--- |
| CMMS 书目信息（作者、题名、期刊、卷期、页码、年份、DOI） | 文献核查与复现 | **已核实（一次文献全文）** | C. Cabrelli, F. Mendivil, U. M. Molter, R. Shonkwiler, *On the Hausdorff $h$-measure of Cantor sets*, *Pacific J. Math.* 217 (2004), No. 1, 45–59, `doi:10.2140/pjm.2004.217.45` | `verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf` 封面及第 45–59 页（`https://msp.org/pjm/2004/217-1/pjm-v217-n1-p04-s.pdf`） |
| CMMS §5 主定理编号与不等式常数 | 文献核查与复现 | **已核实并纠错** | 原文为 **§5, Theorem 3**（正式刊出本第 57–58 页；预印本 `h-sets.pdf` 第 13 页），结论为 $\frac{1}{32}\le \mathcal{H}^h(C_a)\le 1$（非增正序列 $\sum a_k=1$） | 逐页核对 `CMMS_PJM_2004_217_45.pdf` pp. 54–58（§5 依次含 Lemma 2, Proposition 6, **Theorem 3**, Proposition 7）及 `h-sets.pdf` pp. 10–14 |
| 论文二中三处 `\cite[\S5, Theorem~5]{CMMS}` | 文献核查与复现 | **已修正并重编译** | 论文二第 143、292、1331 行（修订后行号）全部更正为 `\cite[\S5, Theorem~3]{CMMS}` | `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex` 双遍 `pdflatex` EXIT 0，0 警告，0 Overfull `\hbox` |

## 核对摘要（直接摘自一次文献）

- **预印本**（`verification/reference_pdfs/h-sets.pdf`，共 15 页）：
  - §3：Proposition 1, Definition 1, Proposition 2, **Theorem 1**
  - §4：Proposition 3, Proposition 4, Proposition 5, **Theorem 2**
  - §5（Dimension function，pp. 10–14）：Lemma 2, Proposition 6, **Theorem 3**（p. 13：*"Let $a=\{a_k\}$ be a non-increasing sequence of positive terms such that $\sum a_k = 1$ and $C_a$ the associated Cantor set. Then $C_a$ is an $h$-set. Moreover $\frac{1}{32} \le H^h(C_a) \le 1$"*）, Proposition 7。
- **正式刊出本**（`verification/reference_pdfs/CMMS_PJM_2004_217_45.pdf`，*Pacific J. Math.* Vol. 217, No. 1, Nov. 2004, pp. 45–59）：
  - §3（pp. 47–48）：Proposition 1, Definition 1, Proposition 2, Notation 1, **Theorem 1**
  - §4（pp. 49–54）：Proposition 3, Proposition 4, Proposition 5, **Theorem 2**
  - §5（Dimension function, pp. 54–58）：Lemma 2（p. 55）, Proposition 6（p. 55）, **Theorem 3**（pp. 57–58：*"Let $a=\{a_k\}$ be a nonincreasing sequence of positive terms such that $\sum a_k = 1$ and $C_a$ the associated Cantor set. Then $C_a$ is an $h$-set. Moreover $\frac{1}{32} \le \mathcal{H}^h(C_a) \le 1$, where $\mathcal{H}^h$ is the Hausdorff measure associated to $h$, and $h$ is the dimension function defined on page 54."*）, Proposition 7（p. 58）。

## 教训记录

- 此前某次二次检索/摘要将 CMMS 的该定理误记为 Theorem 5；按 `AGENTS.md` §3 引用纪律，必须以实际打开的正式刊出全文 PDF 为唯一依据，此次复核已彻底纠偏。
