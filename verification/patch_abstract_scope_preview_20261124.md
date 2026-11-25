# E10 摘要口径补丁 · 预览（2026-11-24）

> 任务：`verification/flash_task_briefs_v2_20261124.md` E10「摘要口径补丁脚本（只起草，禁止执行修改）」。
> **状态：只起草。** 本文件与 `paper2_spectral_gap_dimension/patch_abstract_scope_20261124.py` 均为本批次新建文件；脚本从未以 `--apply` 运行；主稿未被改动（dry-run 前后 sha256 一致，见 §5）。

## 1. 一句总判断

补丁脚本已按 E10 规格起草并实跑 dry-run 通过：默认模式只打印锚点行号与将插入的句子、不写任何文件；仅当命令行给 `--apply` 且交互输入 `yes` 才落盘，落盘方式为在锚点句（主稿实测 L157–162）之后**纯插入一行新增句**，脚本幂等、可重复运行。

## 2. 锚点原文与实测行号

rg 实测（命令与输出见 §6）：

- 任务书引用「L157–160」对应锚点句**核心**：起点 L157 `Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector`，核心句止于 L160 `via the pressure formalism remain outside the Lean kernel`；
- 完整锚点句（含括注的审计计数说明）实测止于 **L162** `...total Lean files).`，下一行 L163 起为 `The classification and the first gap...`。**插入点取整句末尾（L162 句末 `).` 之后）。**

锚点原文（主稿 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex` L157–162，逐字照录）：

```latex
Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector
existence input in Theorem~\ref{thm:finite-state-tail} and the Python-executed
open-interval strictness verification of the narrow $m\in\{2,3,4,5,6\}$ brackets
via the pressure formalism remain outside the Lean kernel
(Section~\ref{sec:verification}, $937$ main audited declarations across $134$
Lean files in \texttt{Audit.lean} plus standalone audits across $344$ total Lean files).
```

即：摘要目前的「内核之外内容」自报只列 **2 处**（PF 特征向量存在性输入；Python 执行的开区间严格性验证）。

## 3. 新增句（纯插入，一行）

```latex
Beyond the two items just named, the complete set of portions not resolved here or lying outside the Lean kernel is exactly the four-item list recorded in Section~\ref{sec:verification}: the finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence input in Theorem~\ref{thm:finite-state-tail}, the strictness of the open intervals in Theorem~\ref{thm:residues} and Table~\ref{tab:residues-general} via the cited pressure formalism, the asymptotic rate on the critical boundary $s_0(S)=1/2$ and the exact supercritical leading constant in Theorem~\ref{thm:multi-residue-asymptotic}, and the irrationality of $e+\pi$, which remains an open problem.
```

来源对照：§verification 四项口径整句实测为**主稿 L4390–4402**（rg 证据见 §6；任务书引 L4393–4401 落在其中），起于 L4390 行尾 `The portions not resolved here or lying outside`，止于 L4402 `which remains an open problem.`。新增句把四项逐字照录为：

| # | 四项口径 | 源行号 | 照录说明 |
|---|---|---|---|
| 1 | the finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence input … in Theorem~\ref{thm:finite-state-tail} | L4391–4393 | 源句中「正右特征向量被显式传入 `FiniteStateComplete.lean`」的括注为摘要篇幅省略 |
| 2 | the strictness of the open intervals in Theorem~\ref{thm:residues} and Table~\ref{tab:residues-general} via the cited pressure formalism | L4396–4398 | 源句中「闭区间本身已内核核查（Remark rem:residue-kernel）」的括注省略 |
| 3 | the asymptotic rate on the critical boundary $s_0(S)=1/2$ and the exact supercritical leading constant in Theorem~\ref{thm:multi-residue-asymptotic} | L4399–4401 | 逐字照录 |
| 4 | the irrationality of $e+\pi$, which remains an open problem | L4401–4402 | 逐字照录 |

补全效果：摘要自报由 2 处扩为 §verification 所列 4 处（PF 特征向量、开区间严格性、临界边界渐近率与超临界首项常数、e+π 开放问题声明），与 E10 任务定义一致。

## 4. dry-run 实跑输出样例（逐字粘贴）

命令（PowerShell 5.1，workspace 根目录）：`.venv\Scripts\python.exe paper2_spectral_gap_dimension\patch_abstract_scope_20261124.py`，exit code 0：

```
== patch_abstract_scope_20261124 (task E10) ==
mode          : DRY-RUN (no files will be written)
target        : <repo-root>\paper2_spectral_gap_dimension\paper2_spectral_gap_dimension.tex
target bytes  : 283403
target sha256 : b165952a8899927dfeaa71c332e10db371a013a6f89313d5075a3805e33559ee
newline style : CRLF
anchor start  : line 157  (marker: Only the finite-dimensional ... eigenvector)
anchor end    : line 162  (end marker: total Lean files).)
insertion pos : char offset 10172 (right after the anchor's final ')';
                the new sentence becomes line 163; no existing character moves.

--- anchor original text (verbatim, lines 157-162) ---
Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector
existence input in Theorem~\ref{thm:finite-state-tail} and the Python-executed
open-interval strictness verification of the narrow $m\in\{2,3,4,5,6\}$ brackets
via the pressure formalism remain outside the Lean kernel
(Section~\ref{sec:verification}, $937$ main audited declarations across $134$
Lean files in \texttt{Audit.lean} plus standalone audits across $344$ total Lean files).

--- sentence to be inserted (pure insertion of one new line) ---
Beyond the two items just named, the complete set of portions not resolved here or lying outside the Lean kernel is exactly the four-item list recorded in Section~\ref{sec:verification}: the finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence input in Theorem~\ref{thm:finite-state-tail}, the strictness of the open intervals in Theorem~\ref{thm:residues} and Table~\ref{tab:residues-general} via the cited pressure formalism, the asymptotic rate on the critical boundary $s_0(S)=1/2$ and the exact supercritical leading constant in Theorem~\ref{thm:multi-residue-asymptotic}, and the irrationality of $e+\pi$, which remains an open problem.

--- preview of the patched region (in memory only; new line numbers) ---
  156: and \texttt{Quot.sound}.
  157: Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector
  158: existence input in Theorem~\ref{thm:finite-state-tail} and the Python-executed
  159: open-interval strictness verification of the narrow $m\in\{2,3,4,5,6\}$ brackets
  160: via the pressure formalism remain outside the Lean kernel
  161: (Section~\ref{sec:verification}, $937$ main audited declarations across $134$
  162: Lean files in \texttt{Audit.lean} plus standalone audits across $344$ total Lean files).
  163: Beyond the two items just named, the complete set of portions not resolved here or lying outside the Lean kernel is exactly the four-item list recorded in Section~\ref{sec:verification}: the finite-dimensional linear-algebraic Perron--Frobenius eigenvector existence input in Theorem~\ref{thm:finite-state-tail}, the strictness of the open intervals in Theorem~\ref{thm:residues} and Table~\ref{tab:residues-general} via the cited pressure formalism, the asymptotic rate on the critical boundary $s_0(S)=1/2$ and the exact supercritical leading constant in Theorem~\ref{thm:multi-residue-asymptotic}, and the irrationality of $e+\pi$, which remains an open problem.
  164: The classification and the first gap are a subsequence analogue of a criterion
  165: of Kraaikamp and Liardet. The work is a spin-off of a project on the
  166: irrationality of $e+\pi$ and does \emph{not} resolve that open problem.

== DRY-RUN complete: nothing written. ==
```

## 5. 落盘行为规格与验收自检

- **默认 dry-run 不写文件**：本次实跑后主稿 sha256 复测一致（`b165952a8899927dfeaa71c332e10db371a013a6f89313d5075a3805e33559ee`，283403 bytes）。
- **`--apply` 双重门**：还须交互输入 `yes`（strip 后精确等于），否则打印 ABORTED 不写。
- **落盘 = 纯插入**：在 char offset 10172（L162 句末 `).` 之后）插入 `\r\n` + 新增句（主稿实测为 CRLF 行尾，插入文本沿用同一行尾风格）；写入后程序化验证纯插入（前缀、后缀逐字节相同，长度恰增 `len(insert)`），任一不满足即拒绝。
- **幂等**：标记句 `four-item list recorded in Section~\ref{sec:verification}` 已存在时，dry-run 与 apply 均直接报 already applied，不重复插入。
- **锚点唯一性断言**：`ANCHOR_START`/`ANCHOR_END` 各恰出现 1 次，否则打印 `REFUSED` 并以 exit code 2 退出；apply 前重读磁盘并复核锚点未移动。
- **git status**：`git status --porcelain=v1` 无 ` M` 行（快照见 §6）；主稿未被本任务修改。
- **诚实分类**（AGENTS.md §2）：本补丁属「文献核查与复现（第 5 类）：自报口径整理」——只把摘要的自报补全到 §verification 已写明的四项口径，**不改变任何定理内容，不构成数学新结果**；它没做到什么：不解决 e+π 无理性问题本身，§verification 四项内核之外状态也不因这句自报而改变。

## 6. 证据（命令与输出，2026-11-24 实测）

锚点行号（rg）：

```
$ rg -n "Only the finite-dimensional|remain outside the Lean kernel|total Lean files\)|The classification and the first gap" paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex
157:Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector
160:via the pressure formalism remain outside the Lean kernel
162:Lean files in \texttt{Audit.lean} plus standalone audits across $344$ total Lean files).
163:The classification and the first gap are a subsequence analogue of a criterion
```

§verification 四项口径行号（rg）：

```
$ rg -n "The portions not resolved here or lying outside|which remains an open problem|TODO before submission" paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex
4390:(\texttt{verification/\allowbreak colab\_\allowbreak rebuild\_\allowbreak audit\_\allowbreak 20261123.md}), ... The portions not resolved here or lying outside
4402:which remains an open problem.
```

（输出中段省略号处为同一行内的重建记录文字，未改动；完整行文见主稿 L4390–4402。）

dry-run 后哈希复测：

```
$ .venv\Scripts\python.exe -c "import hashlib; from pathlib import Path; b=Path('paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex').read_bytes(); print('bytes', len(b)); print('sha256', hashlib.sha256(b).hexdigest())"
bytes 283403
sha256 b165952a8899927dfeaa71c332e10db371a013a6f89313d5075a3805e33559ee
```

git status 快照（写入本预览文件之后、收尾自检时抓取）：

```
$ git status --porcelain=v1
?? "PI_\346\226\260\345\212\252\345\212\233\346\226\271\345\220\221\344\270\216\350\267\257\345\276\204_20261124.md"
?? development_plan_20261124.md
?? integrated_advancement_plan_20261124.md
?? paper2_numeric_check_20261124.py
?? paper2_numeric_check_20261124_output.txt
?? paper2_spectral_gap_dimension/patch_abstract_scope_20261124.py
?? paper2_split_plan_20261124.md
?? verification/T6_critical_scaling_conjecture_20261124.md
?? verification/bowen_dependency_inventory_20261124.md
?? verification/critical_point_scan_20261124.jsonl
?? verification/critical_point_scan_20261124.log
?? verification/critical_point_scan_20261124.py
?? verification/critical_point_scan_20261124.stdout.txt
?? verification/critical_point_scan_20261124_config.json
?? verification/critical_point_scan_20261124_config_deep.json
?? verification/critical_point_scan_20261124_config_ext.json
?? verification/critical_point_scan_20261124_diagnostics.md
?? verification/critical_point_scan_20261124_diagnostics_v2.md
?? verification/critical_point_scan_addendum_20261124.md
?? verification/critical_point_scan_addendum_extract_20261124.py
?? verification/critical_point_scan_analyze_20261124.py
?? verification/critical_point_scan_record_20261124.md
?? verification/critical_scaling_check_20261124.py
?? verification/critical_scaling_check_20261124_output.md
?? verification/critical_scaling_check_20261124_output_v2.md
?? verification/flash_task_briefs_20261124.md
?? verification/flash_task_briefs_v2_20261124.md
?? verification/generalization_obstacle_list_20261124.md
?? verification/journal_landscape_20261124.md
?? verification/journal_landscape_evidence_20261124.md
?? verification/paper2_section_map_20261124.csv
?? verification/patch_abstract_scope_preview_20261124.md
$ git diff --stat
（空输出）
$ git diff --name-only
（空输出）
```

结论：无任何 ` M` 行；被跟踪文件零改动（`git diff` 为空）；本任务新增的两个文件（`patch_abstract_scope_20261124.py`、`patch_abstract_scope_preview_20261124.md`）均以 `??` 出现。其余 `??` 条目为此前批次已存在的未跟踪文件（在本任务首个快照中即已出现，非本任务产出）。

### 验收自检 git status 快照

已实抓并粘贴于上（2026-11-24，收尾自检，`git status --porcelain=v1` 无 ` M` 行）。
