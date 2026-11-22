# thm:windows Lean 验证注记提案（2026-11-21，只读起草，tex 零改动）

> 一句总判断：计数核心三件套及 32 条 WindowMobiusCount 声明已与审计 log 逐字对上，下方 remark 可原样采用；Frostman 质量分布组装仍为纸面，remark 内已明确排除。
> 类别：第 5 类（文献核查与复现）加形式化引理注记。本提案只新增本文件，tex 正文未动（见第五节）。

## 一、remark 全文（英文，与论文语言一致）

```latex
\begin{remark}[Machine-checked counting core for Theorem~\ref{thm:windows}]\label{rem:windows-lean}
The counting core used in the proof of Theorem~\ref{thm:windows}---the M\"obius inversion identity \texttt{WindowMobiusCount.coprime\_count\_eq}, the partial-sum lower bound $359/900$ in \texttt{WindowMobiusCount.moebius\_partial}, and the rectangle-counting lower bound $R^2/10000$ (for $R \ge 10^6$) in \texttt{WindowMobiusCount.coprime\_count\_ge} for the rectangle $[0.34R,0.36R]\times[0.20R,0.22R]$---has been verified by the Lean~4 kernel (Lean~4.35.0 with mathlib~v4.35.0), together with its supporting lemmas ($32$ \texttt{WindowMobiusCount.*} declarations in total). All $32$ declarations depend only on the Lean base axioms \texttt{propext}, \texttt{Classical.choice}, and \texttt{Quot.sound}, as audited with \texttt{\#print axioms} in \texttt{Audit.lean} (see \texttt{verification/audit\_window\_wired\_20261121.log}, with zero \texttt{sorryAx}); no project-added axioms are used. The Frostman mass-distribution assembly that converts this counting input into the dimension conclusions remains paper mathematics and is not machine-checked.
\end{remark}
```

## 二、建议插入位置

首选：tex 第 2836 行 \end{proof} 之后、第 2838 行之前，即 Theorem no-short-dim 证明结尾后：

```
2834: Theorem short-ae implies Lebesgue measure zero (since
2835: almost every x has r_j(x)<=1 infinitely often).
2836: \end{proof}
2837: (空行，插入 remark)
2838: In particular, the set with eventually r_j>=3 has Lebesgue
```

理由：L2783 明写 By the same Moebius inversion calculation as in Theorem thm:windows，该证明是计数核心的第二个使用点；放在此处一个注记同时覆盖两处使用，且紧邻证明结尾、文体与既有 remark 一致。备选：若编辑只想注记 thm:windows 本体，可改插第 2596 行证明结尾之后、For related spectra 段之前；remark 正文无需改动。

label rem:windows-lean 经全文检索无冲突（既有仅 rem:linear-indep、rem:unweighted、rem:gauge-scale、rem:poly-gauge-scale）。

## 三、核对清单

| 断言 | 结论 | 证据 | 来源（2026-11-21） |
|---|---|---|---|
| coprime_count_eq 存在且仅依赖基础三公理 | 已验证 | log L687 公理行 propext/Classical.choice/Quot.sound | audit_window_wired_20261121.log |
| moebius_partial 即 359/900 部分和下界 | 已验证 | log L696 公理行；Partial.lean L75-77 给出 359/900 下界 | audit log ＋ WindowMobiusPartial.lean |
| coprime_count_ge 即 R2/10000 下界（R>=10^6） | 已验证 | log L712 公理行；MainBound.lean L165-167 阈值与界 | audit log ＋ WindowMainBound.lean |
| 32 条 WindowMobiusCount 声明全部基础三公理 | 已验证 | Select-String 命中 32 行（log L681-L712），无白名单无自加 | 本次实测（声明数 531=499+32 采 merge 记录口径） |
| 零 sorryAx | 已验证 | Select-String sorryAx 命中 0 | 本次实测 audit log |
| Lean 4.35.0 加 mathlib v4.35.0 | 已验证 | lean-toolchain L1；lakefile.toml L12-15 mathlib rev | epi_formal/lean-toolchain、lakefile.toml |
| 矩形 0.34R-0.36R 乘 0.20R-0.22R | 已验证（纸面） | tex L2447-2450 矩形定义 | paper2 tex |
| Frostman 组装仍为纸面 | 共识 | AI 节明写 beyond verified counting core 未机检；merge 四同 | tex L3281-3289 ＋ merge 记录 |
| 与 AI 节 341/531 口径一致 | 共识 | AI 节 341 本篇声明／531 全项目声明；32 条为其子集，该节无需修改 | tex L3273-3280 |

注：remark 中具名的 Lean 定理仅用上表三条（均与 log 逐字一致）；其余 29 条以 supporting lemmas（32 declarations in total）概括，未具名即无误引风险。

## 四、与既有声明节的一致性

tex L3281-3289 已有总述（verified counting core；assembly 未机检）。本 remark 是其在定理使用点的局部落地：措辞（kernel verified／audited with print-axioms in Audit.lean／仅基础三公理／Frostman 仍为纸面）与 AI 节逐项对应，无口径冲突；采用后 AI 节无需修改。

## 五、未改动声明

本次只读加新建本提案文件；tex 正文未执行任何写入；未运行任何构建（lake build／lake env lean 均未跑），版本与审计结论全部来自既有 log、merge 记录与本次只读 grep／Select-String 实测。
