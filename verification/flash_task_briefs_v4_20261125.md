# flash 执行任务书 v4（2026-11-25）——hyp:tail 闭合、主稿 B 压页、全线重编译与提交

> **指挥关系**：主会话（指挥）已完成数学路线分析与 Lean 三文件验收；本文件是给 GLM-5.3-Flash 的执行命令，每条含**目标、方法、路径**。执行结果由主会话逐条验收，不合格打回。
> **全局规则（每条适用）**：
> - 本批**允许** `pdflatex`、`lake`（只读/构建）、`git add/commit/push`（仅 E22，且必须全检查通过后）；`git status/diff/log` 随时可用。
> - **只增不减**：仓库既有文件（`paper2_spectral_gap_dimension.tex`、`refs.tex`、全部旧 `.lean`、旧 md）不得修改；**允许按本任务书逐字修改**的本会话新建文件：`split/src_sections/sec-critical-scaling.tex`、`split/frontmatter-2C-v3-20261124.tex`、`paper2_spectral_gap_dimension/BUILD_LOG_20261124.md`、`master_overview_20261124.md`（只准追加）、`README.md`（只准追加）。
> - 写文件统一 UTF-8 无 BOM：`[IO.File]::WriteAllText($p,$s,[Text.UTF8Encoding]::new($false))`。
> - 顺序：E17 → E18 → E19 → E20 → E21 → E22。每条完成即落盘并回报；E22 之前任何检查不过则停在那里回报，不得提交。
> - 回答 ≤800 字，列出产出/修改文件与关键命令输出（页数、exit code、axioms 行）。

---

## E17｜把 Hypothesis hyp:tail 升级为已证引理（指挥已给出全部插入文本）

- **目标**：`sec-critical-scaling.tex` 中删去「Hypothesis（条件假设）」及其全部引用；Theorem `thm:critical-scaling` 与 Corollary `cor:critical-exp` 由条件结果升为定理；同步更新该文件头状态标签、frontmatter-2C-v3 与构建日志。
- **方法**：按下述五步做**精确字符串替换**（用 Python `str.replace`，替换前 `assert old in s`；每次替换后立即回写）。所有插入文本**逐字照抄本任务书**，不得改写。
- **路径**：`paper2_spectral_gap_dimension/split/src_sections/sec-critical-scaling.tex`、`paper2_spectral_gap_dimension/split/frontmatter-2C-v3-20261124.tex`、`paper2_spectral_gap_dimension/BUILD_LOG_20261124.md`。

**第 1 步（替换文件头状态标签）**：把
```
%   Theorem~\ref{thm:critical-scaling} [CONDITIONAL] proved modulo hypothesis (H).
%   Corollary~\ref{cor:critical-exp} [CONDITIONAL] consequence of (H).
```
替换为
```
%   Lemma~\ref{lem:resolvent-uniform} [THEOREM] proved here (elementary estimates).
%   Lemma~\ref{lem:master}       [THEOREM] proved here modulo the repo criterion.
%   Theorem~\ref{thm:critical-scaling} [THEOREM] proved here modulo the repo criterion.
%   Corollary~\ref{cor:critical-exp} [THEOREM] consequence of the Theorem.
```

**第 2 步（删除 Hypothesis，插入两条引理）**：找到从 `\begin{remark}[Hypothesis: uniform tail equation in the critical window]\label{hyp:tail}` 起、到 `\end{remark}` 止的整块（含 `\eqref{eq:tail-uniform}` 公式），整块替换为下文（逐字）：

```latex
\begin{lemma}[Uniform two-sided resolvent expansion]\label{lem:resolvent-uniform}
Let $m\ge 2(\max S+\max B+1)$, put $\Sigma:=1+\max S+\max B$, and write
$h(s):=d\,C_S(2s)\,m^{-2s}\,\zeta(2s)$ for $s\in(\max(s_0,\tfrac12),1]$.
Then for every such $s$ and every $x\in[0,1]$,
\begin{equation}\label{eq:resolvent-uniform}
\mathcal L_{s,\mathcal A_{m,S,B}}V_{S,s}(x)
=V_{S,s}(x)-1+h(s)\,(1+\rho(s,x)),\qquad |\rho(s,x)|\le C_0\,\Sigma/m,
\end{equation}
where $C_0$ is an absolute constant.
\end{lemma}

\begin{proof}
The $S$-branches contribute $V_{S,s}(x)-1$ by the multi-branch resolvent
identity \eqref{eq:multi-resolvent-branch} (valid for $s>s_0(S)$).  Each of the
$d$ large-branch families ($a=r+km$, $r\in S$, $k\ge1$; and $a=km-b$, $b\in B$,
$k\ge1$) is handled identically.  Write $a+x=m(k+\theta)$ with
$|\theta|\le\Sigma/m\le\tfrac12$; the Hurwitz shift obeys
$\sum_{k\ge1}\bigl[(k+\theta)^{-2s}-k^{-2s}\bigr]
\le 2s\,2^{2s+1}\,|\theta|\,\zeta(2s+1)\le C\,\Sigma/m$, the constant being
absolute because $u\,\zeta(1+u)$ is bounded on $(0,2]$; and the test-function
expansion $|V_{S,s}(y)-C_S(2s)|\le 2s\,y\,C_S(2s)$ (mean value theorem over
each word, using $p(w)/q(w)=[0;w]\le1$) contributes a relative error
$O\bigl(m^{-1}\zeta(2s+1)/\zeta(2s)\bigr)=O(\Sigma/m)$, since
$\zeta(2s)\ge1$ on $2s>1$.  Summing the $d$ families gives
\eqref{eq:resolvent-uniform}.
\end{proof}

\begin{lemma}[Master equation at the critical dimension]\label{lem:master}
Under the assumptions of Lemma~\ref{lem:resolvent-uniform}, let
$s^*:=\dimH F_{m,S,B}$ and $\varepsilon_m:=2s^*-1$.  Then
\begin{equation}\label{eq:master}
\bigl|\,d\,C_S(1+\varepsilon_m)\,m^{-1-\varepsilon_m}\,\zeta(1+\varepsilon_m)-1\,\bigr|
\le \bar\delta_m:=C_1\,\Sigma/m+2\,\ee^{-c_0m^2},
\end{equation}
where $c_0:=d\,C_S(2)/3>0$ and $C_1$ is absolute.
\end{lemma}

\begin{proof}
The function $h$ is finite, continuous and strictly decreasing on
$(\max(s_0,\tfrac12),1]$, tends to $+\infty$ at the left endpoint (through the
pole of $C_S$ at $2s_0$ or of $\zeta$ at $1$), and $h(1)<1$ for all large $m$
(the quantitative pole bound $C_S(2(s_0+\delta))\le 32/\delta$ used in
Theorem~\ref{thm:multi-residue-asymptotic}(v) gives $h(1)\le 64\,d\,\zeta(2)/m^2$).

\emph{Upper side.}  If $h(s)(1+C_0\Sigma/m)\le1$, then
\eqref{eq:resolvent-uniform} makes $V_{S,s}$ a subsolution,
$\mathcal L_{s,\mathcal A}V\le V$, whence $\dimH F_{m,S,B}\le s$ by the upper
direction of the transfer-operator criterion of
Theorem~\ref{thm:residues-general}(ii) (kernel-checked as
\texttt{step\_cert\_upper\_sound}; the paper's own proof of part~(i) applies
this direction to $V_{S,s}$ itself).  Consequently
$h(s^*)\ge1/(1+C_0\Sigma/m)$.

\emph{Lower side.}  Put $K:=\lceil\ee^{m^3}\rceil$,
$D_K:=S\cup\{r+km:\ r\in S,\ 1\le k\le K\}\cup\{km-b:\ b\in B,\ 1\le k\le K\}
\subseteq\mathcal A_{m,S,B}$ (a finite subalphabet) and
$h_K(s):=d\,C_S(2s)\,m^{-2s}\sum_{k\le K}k^{-2s}$.  The truncated test function
$v_N:=\sum_{j<N}\mathcal L_{s,S}^{\,j}1$ satisfies
$\mathcal L_{s,S}v_N=v_N-1+\mathcal L_{s,S}^{\,N}1\ge v_N-1$, and the $D_K$-tail
contributes $h_K(s)(1+O(\Sigma/m))$ by the estimates of
Lemma~\ref{lem:resolvent-uniform}; hence $\mathcal L_{s,D_K}v_N\ge v_N$
whenever $h_K(s)(1-C_2\Sigma/m)\ge1$, and the finite-subalphabet lower
direction of Theorem~\ref{thm:residues-general}(ii) (kernel-checked as
\texttt{step\_cert\_lower\_sound}) yields $\dimH F_{m,S,B}\ge s$.

It remains to compare $h_K$ with $h$.  Let $\varepsilon_0$ be the unique
solution of $h(\varepsilon_0)=1$.  Since
$f(\varepsilon):=d\,C_S(2)\,m^{-1-\varepsilon}/\varepsilon$ is a decreasing
lower bound for $h$ and $f(\varepsilon_0)\le h(\varepsilon_0)=1$, we get
$\varepsilon_0\ge c_0/m$ with $c_0=d\,C_S(2)/3$ for all large $m$ (the factor
$m^{-\varepsilon_0}\ge\tfrac12$ holds because $\varepsilon_0\log m\to0$).
Hence for all $\varepsilon\ge\varepsilon_0/2$ the truncation ratio obeys
$\mathrm{trunc}(\varepsilon):=\sum_{k>K}k^{-1-\varepsilon}/\zeta(1+\varepsilon)
\le C\,K^{-\varepsilon}\le C\,\ee^{-c_0m^2}$.  Moreover $h_K(\varepsilon_0)
=1-\mathrm{trunc}(\varepsilon_0)\le1$ together with $|h_K'|/h_K\ge2\log m$ (the
$m^{-2s}$ factor dominates) gives $|\varepsilon_K-\varepsilon_0|\le
C\ee^{-c_0m^2}/\log m$ for the $h_K$-root $\varepsilon_K$, so
$\mathrm{trunc}(\varepsilon_K)\le2C\ee^{-c_0m^2}$ as well.  The sandwich
$s_K\le s^*\le s_-$ between the two criteria and the monotonicity of $h$ now
give $h(s^*)\le h(s_K)\le(1-C_2\Sigma/m)^{-1}(1-\mathrm{trunc}(\varepsilon_K))^{-1}$,
which is \eqref{eq:master}.
\end{proof}
```

**第 3 步（改写定理与推论的陈述与证明）**：
- 把定理陈述里的 `Assume Hypothesis~\ref{hyp:tail}. Let $\eta:=1-2s_0(S)$ and` 替换为 `Let $\eta:=1-2s_0(S)$ and`。
- 把 Corollary 陈述里的 `Assume Hypothesis~\ref{hyp:tail} and let $s_0(S)=\frac12$` 替换为 `Let $s_0(S)=\frac12$`。
- 在定理证明的开头 `\begin{proof}` 之后、`Put $\varepsilon:=...` 之前插入（逐字）：

```latex
\emph{A priori bounds.}  $\varepsilon_m>0$ since $\dimH F_{m,S,B}>\tfrac12$
(Theorem~\ref{thm:multi-residue-asymptotic}(ii)), and
$\varepsilon_m\le 2\max\bigl(-\eta,\,C\sqrt{d/m}\bigr)$ with $C$ absolute: at
$\bar\varepsilon:=2\max(-\eta,\,24\sqrt{d/m})$ the pole bound
$C_S(1+\varepsilon)\le64/(\varepsilon+\eta)$ and
$\zeta(1+\varepsilon)\le3/\varepsilon$ give $h(\bar\varepsilon)\le\tfrac16
<1/(1+\bar\delta_m)$, so $s^*$ lies below the $h$-threshold.  In particular
$\varepsilon_m\to0$ and $\varepsilon_m+\eta\to0$ along any sequence with
$m\to\infty$ and $\eta m^{1/2}\to x\in\R$.

\emph{The implicit equation.}  Lemma~\ref{lem:master} gives
$d\,C_S(1+\varepsilon_m)\,m^{-1-\varepsilon_m}\zeta(1+\varepsilon_m)
=1+O(\bar\delta_m)$.  Lemma~\ref{lem:pole}(e) rewrites
$C_S(1+\varepsilon_m)=\kappa/(\varepsilon_m+\eta)+O(1)$ (legitimate because
$\varepsilon_m+\eta\to0$), part~(iii) of
Theorem~\ref{thm:multi-residue-asymptotic} rewrites
$\zeta(1+\varepsilon_m)=\varepsilon_m^{-1}+\gamma+O(\varepsilon_m)$, and the
relative errors so introduced are
$O(\varepsilon_m+\eta)+O(\varepsilon_m)+O(\bar\delta_m)=o(1)$.  Hence
\begin{equation}\label{eq:implicit}
\varepsilon_m\,(\varepsilon_m+\eta)\,m^{1+\varepsilon_m}=d\,\kappa\,(1+o(1)).
\end{equation}
```

- 定理证明中原来那句 `By Lemma~\ref{lem:pole}(e),` 起的推导若与上文重复，保留原样（原文代入法 `ε=m^{-1/2}u_m...` 继续有效，只是其依据从 Hypothesis 换成 \eqref{eq:implicit}；把原证明里引用 `Hypothesis~\ref{hyp:tail}` 或 `\eqref{eq:tail-uniform}` 的字样全部改为 `\eqref{eq:implicit}` 或 `Lemma~\ref{lem:master}`）。
- 删除「What this section proves and what it does not」小节中含 `Hypothesis~\ref{hyp:tail}` 的两个条目，替换为（逐字）：
```latex
\item \textbf{Proved.} Lemma~\ref{lem:resolvent-uniform} and Lemma~\ref{lem:master}
(the uniform resolvent expansion and the master equation, with
$K=\lceil e^{m^3}\rceil$ on the lower side); hence the joint scaling limit
Theorem~\ref{thm:critical-scaling} and the critical exponent
Corollary~\ref{cor:critical-exp}, both modulo the repo's transfer-operator
criterion (Theorem~\ref{thm:residues-general}(ii), whose step-certificate
soundness is kernel-checked as \texttt{step\_cert\_upper\_sound} and
\texttt{step\_cert\_lower\_sound}).
\item \textbf{Not proved.} The supercritical leading constant
(Proposition~\ref{prop:supercritical-constant}); the continuity of $\kappa(S)$
in $S$; the existence of an integer set $S$ with $s_0(S)=\frac12$ exactly; any
Lean formalization of the critical-scaling layer beyond the pole axiom and the
scaling-function identity.
```

**第 4 步（frontmatter-2C-v3 同步）**：
- 摘要中 `and, conditionally on a uniform tail
estimate, the critical exponent $1/2$ with amplitude $\sqrt{d\kappa(S)}/2$ and
no log correction.` 替换为 `and the critical exponent $1/2$ with amplitude
$\sqrt{d\kappa(S)}/2$ and no log correction.`
- 诚实声明段中 `The scaling theorem and the critical exponent are proved only modulo
the uniform tail estimate stated as Hypothesis~\ref{hyp:tail}; that hypothesis
is not established here.` 替换为 `The scaling theorem and the critical exponent are proved from the
master equation (Lemma \texttt{lem:master}), whose lower side uses the
finite-subalphabet transfer-operator criterion; that criterion's step-certificate
soundness is kernel-checked, but the analytic estimates of the critical-scaling
section are not Lean-formalized.`

**第 5 步（构建日志追加）**：在 `BUILD_LOG_20261124.md` 末尾追加一行：
`- 2026-11-25 E17：Hypothesis hyp:tail 已升级为 Lemma lem:resolvent-uniform + lem:master（指挥给出文本，flash 执行替换）；thm:critical-scaling / cor:critical-exp 升为定理（modulo 仓库判定准则）。`

**验收**（主会话执行）：替换后 `rg -n "hyp:tail|Hypothesis" sec-critical-scaling.tex` 命中 0；花括号配对；E19 编译通过。

## E18｜主稿 B 压到 ≤35 页

- **目标**：`split/2B_general_theory/paper2B_unified_draft_20261124.tex` 编译后 ≤35 页（现为 36）。
- **方法**：两级压缩，每级后重编译看页数，达标即停：
  1. 在 `paper2B_unified_draft_20261124.tex` 中把 `\input{../src_sections/sec-num-2A.tex}` 替换为如下 6 行（逐字）：
```latex
% Numerical notes for the 2A block are consolidated; full tables remain in the
% companion manuscript and in sec-num-2A.tex.
\begin{remark}[Numerical evidence for the $\ee$-recurrence]\label{rem:num-2A}
The two-term and three-term expansions of this paper are corroborated, for the
selected denominators of $\ee$, by the $32$-digit \texttt{mpmath} Chebyshev
collocation pipeline of the companion manuscript (\texttt{verify\_paper2\_\
extensions.py}, \texttt{verify\_residue\_multi\_asymptotic.py}), including the
closed $N=512$ kernel brackets and the $m\le16384$ residual tables.
\end{remark}
```
  2. 若仍为 36 页：在 `frontmatter-2B-v3-20261124.tex` 中把诚实声明段（`\section*{Honesty statement...}` 起到 companion 句之前的整段正文）用 `{\small ...}` 包裹。
- **路径**：上述两文件 + 重编译在 `split/2B_general_theory/` 目录执行 `pdflatex -interaction=nonstopmode paper2B_unified_draft_20261124.tex` 两遍。
- **验收**：`Output written on ... (35 pages` 或更少；`rg -c "undefined" *.log` 为 0；若做了第 2 级，`frontmatter-2B-v3` 的花括号配对。

## E19｜全线重编译（v3 重生成 + 主稿 A + 三轨回归）

- **目标**：E17/E18 改动后全部构建线通过。
- **方法**：
  1. `.venv\Scripts\python.exe paper2_spectral_gap_dimension\patch_t6_integration_20261124.py --apply`（重生成 v3；确认输出含 `original manuscript SHA-256 unchanged`）。
  2. 在 `paper2_spectral_gap_dimension/` 执行 `pdflatex -interaction=nonstopmode -halt-on-error paper2_spectral_gap_dimension_v3_20261124.tex` 两遍；记录页数与 `rg -c "undefined|Overfull" paper2_spectral_gap_dimension_v3_20261124.log`。
  3. 在 `split/2C_windows_residues_finstate/` 重编译 `paper2A_critical_scaling_draft_20261124.tex` 两遍，记录页数。
  4. 三轨回归：`2A_core_gauge_trichotomy/paper2A_draft.tex`、`2B_general_theory/paper2B_draft.tex`、`2C_windows_residues_finstate/paper2C_draft.tex` 各编译一遍，记录页数（预期 24/15/25 不变）。
- **路径**：如上各目录。
- **验收**：五条线 exit=0；v3 页数应 ≤70；主稿 A 页数应 ≤31；无 undefined 引用。任何一条失败：贴出日志最后 20 行并停下回报。

## E20｜lake build 核验

- **目标**：确认整个 Lean 库（含新模块 Paper2A/B/C.lean）构建通过。
- **方法**：读 `epi_formal/.lake` 之上的构建结果：若后台日志 `.zwork/background/2026-11-25T02-37-36-665Z-rcc7ys.log` 为空或不存在运行中进程，则在 `epi_formal/` 重跑 `lake build 2>&1 | Select-Object -Last 15`（可能需要数分钟）；随后执行 `lake env lean EpiFormal/Paper2C.lean` 并确认输出含三行 `#print axioms`：`scaling_function_identity` 与 `paper2C_phase_transition` 仅 `[propext, Classical.choice, Quot.sound]`，`C_S_pole_decomposition` 含自身。
- **路径**：`epi_formal/`。
- **验收**：`lake build` exit=0（或无 error 行）；三条 axioms 行原文。

## E21｜README 更新（只准追加）

- **目标**：`README.md` 末尾追加一节「2026-11-24/25 增补」，写明：这次做了什么、没做到什么、建议、文件结构与对应关系。
- **方法**：追加（逐字框架，其中数据从 `BUILD_LOG_20261124.md` 与 `master_overview_20261124.md` §7 抄录真实数字，不许编造）：
  - **做了什么**：T6 临界标度节（极点分解定理 + 主方程 + 标度极限定理，均 modulo 仓库判定准则）；尾方程排版错误修正（m^{-ε}→m^{-1-ε}，v3）；旧 C2 固定 η 形式证伪（1.193 复算）；两主稿装配（A=2C+T6 30 页；B=2A+2B 36→35 页，e 降旗舰推论）；三份 paper-level Lean 接口文件（Paper2A/B/C.lean，含一条新白名单公理 C_S_pole_decomposition 与内核已证的 scaling_function_identity）；五条编译线 + lake build。
  - **没做到什么**：超临界常数仍是猜想；T6 分析层未 Lean 形式化（仅公理化接口）；主稿 tex 原件未改（v3 为新文件）；s_0=1/2 精确集存在性未解。
  - **建议**：见 master_overview §7「未完成（下一步）」四条，原文照录。
  - **文件结构**：一张表，行=（v3 集成稿、主稿 A 草案、主稿 B 草案、sec-critical-scaling.tex、refs-addendum、Paper2A/B/C.lean、patch_t6_integration.py、BUILD_LOG、verify_c2_discrepancy.py、deep_research_and_polish.md），列=（路径、对应论文/模块、内容简介、与主稿行号对应关系）。
- **路径**：`README.md`（追加，不改既有内容）。
- **验收**：追加节存在且数字与 BUILD_LOG 一致；`git diff README.md` 只有新增行。

## E22｜全部检查通过后提交并推送

- **目标**：把本轮全部产物提交到 `main` 并推送 `origin`（`https://github.com/Kisketch/epi-work-complete.git`）。
- **方法**（前置条件：E17–E21 全部验收项通过）：
  1. `git add verification paper2_spectral_gap_dimension epi_formal/EpiFormal epi_formal/EpiFormal.lean master_overview_20261124.md README.md`
  2. `git status --porcelain=v1` 检查已暂存清单：**不得包含** `Python/`、`paper2_numeric_check_20261124.py`、`paper2_numeric_check_20261124_output.txt`；若含，`git restore --staged` 对应路径。
  3. `git commit -m "论文二 T6 临界标度：极点分解+主方程+标度极限定理（modulo 仓库准则）；两主稿装配与压页；Paper2A/B/C.lean 接口与公理；全线编译与 lake build（2026-11-25）"`
  4. `git push origin main`；记录 push 输出末 3 行。
  5. `git log --oneline -2` 与 `git status` 确认干净（未跟踪仅剩 Python/ 与 paper2_numeric_check 等 PI 待定项）。
- **路径**：仓库根。
- **验收**：commit 与 push exit=0；远端分支前进 1 个提交。

---

## 主会话保留（不由 flash 做）

- E17 插入文本的数学正确性（已由指挥负责）；验收时逐条 diff 核对替换是否逐字。
- 提交信息措辞与是否拆分提交的最终裁量（若 flash 回报有异常，打回重做，不代做）。
