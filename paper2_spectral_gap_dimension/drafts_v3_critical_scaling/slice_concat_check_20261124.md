# E6 切片逐字节核对报告（slice concat check）—— 2026-11-24

## 一句总判断

**一致**：按固定顺序把 11 个基础切片按字节拼接后，SHA-256 与主稿 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex` 完全相同（两者均为 283,403 字节），即拼接与主稿**逐字节一致**，**不存在首差异行**；11 个切片首尾衔接、无重叠无遗漏，恰好覆盖主稿全部 4,463 行。

诚实分类：本结论属 AGENTS.md 分类法第 5 类（对既有切片工程做核查与复现）/第 4 类（有限机器校验），**不构成任何数学进展**，也不是对 $e+\pi$ 问题的任何推进。

## 两个 SHA-256 原文（实际命令输出）

| 对象 | 字节数 | SHA-256 |
|---|---:|---|
| 11 个基础切片按序拼接（MemoryStream 字节拼接） | 283,403 | `b165952a8899927dfeaa71c332e10db371a013a6f89313d5075a3805e33559ee` |
| 主稿 `paper2_spectral_gap_dimension.tex`（Get-FileHash） | 283,403 | `b165952a8899927dfeaa71c332e10db371a013a6f89313d5075a3805e33559ee` |

- `equal=True`
- **结论：一致（逐字节相同，非仅末尾换行等价）。**
- **首差异行：无**（哈希相等，逐字节比较不可能存在差异行）。

## 复核环境与实测基线

- 主稿：4,463 行 / 283,403 字节；首行 `\documentclass[11pt]{article}`（主稿第 1 行），末非空行 `\end{document}`（主稿第 4,463 行）。
- 主稿换行：CR=4,463、LF=4,463、孤立 LF=0，即全部 CRLF、无孤立 CR/LF。
- 切片目录：`paper2_spectral_gap_dimension/split/src_sections/`，共 28 个 `.tex`。
- 主稿自旧版（SLICE_LOG.md 记录的 4,064 行 / 253,919 字节）已增长，故 `split/src_sections/slice_index.csv` 所记行区间已陈旧（如记 sec-preface 为 1–389 / 24,898 字节，而本次实测该文件为 416 行 / 27,015 字节）；本次为现行主稿重建索引，未改动旧索引。

## 方法（所有行号/哈希均来自下列实际执行的 PowerShell 命令输出）

在 workspace 根目录（PowerShell 5.1）执行，要点：①`Get-ChildItem` 列 28 个 .tex 及字节数；②对每个切片取首行与末非空行，在主稿按整行 `-ceq` 精确匹配定位；③相邻切片「止行+1=下一起行」核对；④`MemoryStream` 按序字节拼接 + `SHA256` 与主稿 `Get-FileHash` 比对（无临时文件落盘）；⑤逐切片做「主稿行区间字节 == 切片文件字节」的直接比对。关键命令原文：

```powershell
# 拼接 + 双哈希（实际输出见上表；equal=True）
$order='sec-preface','sec-class','sec-spectrum','sec-finite','sec-weights','sec-gauge','sec-growing','sec-windows','sec-resasymp','sec-num','sec-verification'
$base='paper2_spectral_gap_dimension/split/src_sections'
$mainP=(Resolve-Path 'paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex').Path
$ms=New-Object System.IO.MemoryStream
foreach($n in $order){ $fb=[System.IO.File]::ReadAllBytes((Join-Path $base ($n+'.tex'))); $ms.Write($fb,0,$fb.Length) }
$sha=[System.Security.Cryptography.SHA256]::Create()
$h1=[System.BitConverter]::ToString($sha.ComputeHash($ms.ToArray())).Replace('-','').ToLower()
$h2=(Get-FileHash -LiteralPath $mainP -Algorithm SHA256).Hash.ToLower()
# 实际输出：concat_total_bytes=283403 / equal=True

# 逐切片字节级区间核验（Test-Span：主稿第 s..e 行的字节序列与切片文件字节逐一比较）
# s = 主稿中切片首行的精确匹配命中行；e = s + 切片行数 - 1
# 实际输出见下表 byteExact 列，11/11 全部通过
```

## 11 个基础切片明细（拼接顺序；行区间含切片文件所含的末尾空行）

| # | 文件 | 字节 | 行数 | 主稿区间 | 首行（截断）→主稿行 | 末非空行（截断）→主稿行 | 字节级核验 |
|---|---|---:|---:|---|---|---|---|
| 1 | sec-preface.tex | 27,015 | 416 | 1–416 | `\documentclass[11pt]{article}` →1 | `zero-set $\{x:j\|Q_jx\|\to0\}$…` →415（416 为空行） | ✓ 1–416 |
| 2 | sec-class.tex | 3,792 | 88 | 417–504 | `\section{Classification and initial spectral gap}` →417 | `only \texttt{propext}, \texttt{Classical.choice}…` →503（504 空行） | ✓ 417–504 |
| 3 | sec-spectrum.tex | 6,666 | 117 | 505–621 | `\section{Complete spectrum discretization…}` →505 | `$9176$ build jobs) with zero \texttt{sorryAx}…` →620（621 空行） | ✓ 505–621 |
| 4 | sec-finite.tex | 12,099 | 232 | 622–853 | `\section{All finite level sets have dimension zero…}` →622 | `axioms.` →852（853 空行） | ✓ 622–853 |
| 5 | sec-weights.tex | 17,605 | 350 | 854–1203 | `\section{Subcritical weights and exact Hausdorff dimensions}` →854 | `set.` →1202（1203 空行） | ✓ 854–1203 |
| 6 | sec-gauge.tex | 81,834 | 1,339 | 1204–2542 | `\section{Critical levels, exact Hausdorff gauges…}` →1204 | `\texttt{verify\_…poly\_…recurrence\_…2b.py}.` →2541（2542 空行） | ✓ 1204–2542 |
| 7 | sec-growing.tex | 23,867 | 339 | 2543–2881 | `\subsection{Universal extension to arbitrary growing-quotient recurrences}` →2543 | `\texttt{Classical.choice}, and \texttt{Quot.sound} ($0$~\texttt{sorryAx}).` →2880（2881 空行） | ✓ 2543–2881 |
| 8 | sec-windows.tex | 50,787 | 776 | 2882–3657 | `\section{Continued-fraction window constraints and digit residues}` →2882 | `\end{remark}` →3655（主稿命中 11 处：531,867,1625,1662,1972,2341,2468,2778,3334,3655,4026；取 3655，由字节级核验唯一确定）（3656–3657 空行） | ✓ 2882–3657 |
| 9 | sec-resasymp.tex | 31,472 | 395 | 3658–4052 | `\subsection{Resolvent identity, global strict separation…}` →3658 | 末非空行为超长验证句（约 4 KB）→4051（4052 空行） | ✓ 3658–4052 |
| 10 | sec-num.tex | 6,547 | 101 | 4053–4153 | `\section{Numerical evidence}` →4053 | `scaling up to $m=4096$.` →4152（4153 空行） | ✓ 4053–4153 |
| 11 | sec-verification.tex | 21,719 | 310 | 4154–4463 | `\section{Honesty statement, scope, and formal verification}` →4154 | `\end{document}` →4463（无末尾空行） | ✓ 4154–4463 |

行数合计：416+88+117+232+350+1339+339+776+395+101+310 = **4,463**；字节合计 = **283,403**。

## 连续性核对（逐相邻对，「止行+1=下一起行」）

- 416+1=417 ✓；504+1=505 ✓；621+1=622 ✓；853+1=854 ✓；1203+1=1204 ✓；2542+1=2543 ✓；2881+1=2882 ✓；3657+1=3658 ✓；4052+1=4053 ✓；4153+1=4154 ✓
- 起点为第 1 行、终点为第 4,463 行：11 个切片对主稿 **1–4,463 行连续无缝覆盖，无重叠、无遗漏**。

## 其余 17 个节文件（非基础切片）

分类口径（依 `split/README.md`、`split/src_sections/SLICE_LOG.md`）：`shared` = 共享节库成员；`variant` = 三轨派生/编辑变体。其中 8 个经同一字节级核验为主稿的精确行区间提取，已在 CSV `main_start/main_end` 给出实测区间：

| 文件 | note | 实测 |
|---|---|---|
| preamble.tex | shared | 字节级精确提取主稿 1–35 行 |
| frontmatter.tex | shared | 字节级精确提取主稿 36–416 行（与 preamble 衔接：35+1=36） |
| refs.tex | shared | 字节级精确提取主稿 4405–4461 行 |
| sec-num-2A.tex | variant | 字节级精确提取主稿 4053–4096 行 |
| sec-gauge-core.tex | variant | 字节级精确提取主稿 1204–1843 行 |
| sec-finstate.tex | variant | 字节级精确提取主稿 1844–1995 行 |
| sec-poly.tex | variant | 字节级精确提取主稿 1996–2542 行 |
| intro-shared.tex | shared | 未做区间核验（首行在主稿命中 247 处，非唯一锚；记 NA） |
| frontmatter-2A/2B/2C.tex | variant | 变体（首行虽命中主稿 36 行，字节级区间比对不通过，与主稿非逐字节对应；记 NA） |
| intro-2A/2B/2C.tex | variant | 变体（首行在主稿命中 247 处，未尝试区间比对；记 NA） |
| prereq-2B/2C.tex | variant | 变体（首行在主稿无精确命中；记 NA） |
| sec-spectrum-2A.tex | variant | 变体（字节级区间比对不通过；记 NA） |

附注：sec-gauge-core + sec-finstate + sec-poly 三段互为衔接（1843+1=1844；1995+1=1996），并集恰为 sec-gauge 的主稿区间 1204–2542（字节和 39,221+9,069+33,544=81,834），与 SLICE_LOG.md 所记 gauge 二次切分一致。

## 未核到 / 边界说明

- `intro-shared.tex`、`intro-2A/2B/2C.tex`、`prereq-2B/2C.tex` 未做与主稿的区间核对（变体文件非本任务必需项），其与主稿的关系仅标注为 variant/shared，不声称任何区间。
- 本次为**只读核对 + 两个新文件**：未修改、未删除任何既有文件；拼接在内存（MemoryStream）完成，未写临时文件。
