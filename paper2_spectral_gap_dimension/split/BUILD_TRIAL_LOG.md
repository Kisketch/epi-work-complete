# 三轨 draft 试编译记录（BUILD_TRIAL_LOG）

- 环境：MiKTeX 26.5 / MiKTeX-pdfTeX 4.27，Windows PowerShell
- 日期：2026-11-23
- 原则：只读 `.tex`，未修改任何源文件；仅在各轨 `build/` 下产出 `.log`，PDF 与 aux 已作为一次性产物删除
- 编译方式：每轨**单次** `pdflatex -interaction=nonstopmode -file-line-error -output-directory=build <draft>.tex`（工作目录＝各轨目录，以便 `../src_sections/` 解析）

## 0. 前置检查结果

**原版 preamble（`src_sections/sec-preface.tex`）**
- L1：`\documentclass[11pt]{article}`；L2–7：`geometry(margin=1in)`、`amsmath,amssymb,amsthm`、`mathrsfs`、`hyperref(hidelinks)`、`enumitem`、`\emergencystretch=3em`
- L9–18：定理环境 `theorem/lemma/proposition/corollary/conjecture/lemmaA/definition/remark`（共享计数器）
- L20–27：宏 `\R \Z \N \Q \ee \dist \dimH \Lam`
- L36–…：**已经包含 `\begin{document}`、`\maketitle` 与 abstract**
- 结论：该文件**不是纯 preamble 片段**，而是「preamble + 标题 + 摘要 + 正文开头」的整段。任何轨直接 `\input` 它，就等于接管了文档类与 `\begin{document}`。

**bibliography 位置（`src_sections/sec-verification.tex`）**
- L224：`\begin{thebibliography}{99}`（14 条 `\bibitem`）
- L279：`\end{document}`
- 结论：bibliography 与**文档终点**同处一个文件；三轨均未 `\input` 该文件，因此三轨都**缺 bibliography**；若整段接入，则会与各 draft 自带的 `\end{document}` 形成**重复 `\end{document}`**。

**三 draft 当前结构**
| 轨 | 文档类/`\begin{document}` 来源 | 是否含 bibliography | 尾部 `\end{document}` 数 |
|---|---|---|---|
| 2A | `sec-preface.tex`（L1/L36） | 否 | 1（draft L29），无重复 |
| 2B | draft 自带（L15/L16） | 否 | 1（draft L25） |
| 2C | draft 自带（L15/L16） | 否 | 1（draft L24） |

即：**无重复 `\end{document}`**，实际缺陷是 2B/2C **完全没有 preamble 宏包与宏定义**，以及三轨**共同缺 bibliography**。

## 1. 2A 核心规范 / 三分法轨

- 结果：**编译成功，0 error，产出有效 PDF（24 页）**
- 输入：`sec-preface` + `sec-class` + `sec-spectrum` + `sec-finite` + `sec-weights` + `sec-gauge-core`，draft 收尾 `\end{document}`
- 警告：171 个 undefined reference、23 个 undefined citation、22 个 underfull hbox、0 overfull
- 原因：单次编译无 `.aux`，自引用尚未解析；同时 `\ref` 指向未纳入本轨的小节（2B/2C 内容）与 `sec-verification` 的 label；23 个 citation 全部因缺 bibliography（`CMMS`、`MEA`、`BLR`、`Phase1`、`Moreira`、`LimaMoreira` 等）
- 判定：**结构上可独立编译**，唯一硬缺口是 bibliography；二遍编译可消掉大部分自引用

## 2. 2B 一般递推理论轨

- 结果：**编译失败（exit 1），336 error**；nonstopmode 仍吐出 17 页 PDF，但为错排产物，不可用（已删）
- 输入：draft 自带 `article` + `\begin{document}`，后接 `sec-poly` + `sec-growing`
- 错误构成：259 × Undefined control sequence（`\Z \R \ee \eqref` 等，preamble 宏与 `amsmath` 全缺）、12 × Misplaced alignment tab、9 × Environment `proof` undefined，另有 5 × `\begin{document} ended by \end{...}` 的连锁报错
- 警告：44 undefined reference、0 undefined citation（本轨正文未用 `\cite`）、54 overfull
- 判定：**不可独立编译**；根因单一——缺共享 preamble（`amsmath/amssymb/amsthm` + 定理环境 + 宏定义），非内容问题

## 3. 2C 窗口 / 残差 / 有限状态轨

- 结果：**编译失败（exit 1），250 error**；同样吐出 24 页错排 PDF，不可用（已删）
- 输入：draft 自带 `article` + `\begin{document}`，后接 `sec-finstate` + `sec-windows` + `sec-resasymp`
- 错误构成：178 × Undefined control sequence、29 × Misplaced alignment tab、13 × `\begin{document} ended by \end{...}`、7 × Environment `proof` undefined、6 × Environment `theorem` undefined、4 × Missing `$`
- 警告：38 undefined reference、6 undefined citation、61 overfull
- 判定：**不可独立编译**；根因同 2B（缺 preamble），另需 bibliography

## 4. 下一步 wiring 建议（按优先级）

1. **拆 `sec-preface.tex`**：L1–35 → `preamble.tex`（只含 documentclass/宏包/定理环境/宏），L36 起 → `frontmatter.tex`（`\begin{document}`+标题+摘要）。三轨改为 `\input{../src_sections/preamble.tex}`，frontmatter 由各轨自选，避免 2A 被迫继承合并稿标题与摘要。
2. **抽 `refs.tex`**：从 `sec-verification.tex` L224–278 单独切出 `thebibliography` 块（**不带 L279 的 `\end{document}`**），三轨尾部统一 `\input`。这样既补 bibliography，又不引入重复 `\end{document}`。
3. **2A**：仅需补 `refs.tex`；`\end{document}` 保留一份。之后跑两遍 pdflatex，验收标准为 `undefined citations = 0`，残余 undefined reference 应只来自跨轨 label。
4. **2B / 2C**：接入 `preamble.tex` 即可消灭 250/336 条错误中的绝大多数；2C 另需 `refs.tex`，2B 虽当前无 `\cite` 也建议一并接入以统一后续增补。
5. **切片一致性**：`sec-gauge.tex`（原 L1177–2500）仍为整节，三轨分别用已切好的 `sec-gauge-core` / `sec-poly` / `sec-finstate`，本次未触发 `multiply defined`；但不要再让任一轨直接 `\input{sec-gauge.tex}`，否则会重复 label 并越界带入他轨内容。
6. **验收口径**：每轨「两遍 pdflatex 后 0 error、0 undefined citation」为通过线；跨轨 `\ref` 未解析属预期，需在正文改写阶段改为本轨内引用或显式交叉引用说明。

## wiring v2 (2026-11-23)
- preamble.tex(L1-35)+frontmatter.tex(L36-389)+refs.tex(bib L224-276 of verif slice) split, byte-exact.
- 2A 25pp 0 error / 2B 13pp 0 error / 2C 19pp 0 error (pdflatex, track dir as CWD); warnings are cross-track undef refs + under/overfull, expected.
- PDFs/aux removed, logs kept.
