# 伴随论文投稿准备记录

更新于 2026-11-20。稿件沿用现行编号。清单里的模 4 维数“定理 14”在现行稿是定理 16，现行定理 14 是关于短窗口的几乎处处结果。定理 8、11、12 的编号与清单相同。稿件供私人学术复核。

## M1 · 引文与表述

| 条目 | 状态 | 核查 |
|---|---|---|
| A1 | 已核 | BDS 的原始卷页为 Studia Sci. Math. Hungar. 38 (2001), 97–113，工作稿已有正确卷号。复对其余题名和卷页，补上 CLU、Fan–Liao–Wang–Wu 和 Moreira 的正式出版信息，移除未引用条目 |
| A2 | 已改 | p.106 转述的 Kraaikamp–Liardet 判据只为本问题导出 \(1/16\)。谱间隙 \(1/4\) 由本文所用递推给出。稿内的两种常数具有不同角色 |
| A3 | 已核 | 作者原文印刷 p.478 的 Theorem 2.1 给出同质 Moran 集的维数界。稿内加独立书目条目。本文的移位网格构造和上界均有直接证明 |
| A4 | 已核 | Cabrelli 等 §5、Theorem 3 给出 \(1/32\le \mathcal H^h(C_a)\le1\)。引言对照的是这一有限正测度结论 |
| A5 | 已检 | 伴随稿中所引为原始论文、预印本和同行可核查的项目归档。移除旧稿中关于 \(B\pi\) 的有限试验与原问题的推测性段落 |
| A6 | 已改 | 标题与摘要聚焦度量结果。引言用一句话交代分类工具的项目来源。署名留待作者资格和贡献记录确认 |

### 逐项核查入口

- [BDS 原刊全文](https://real.mtak.hu/110616/) · [Kraaikamp–Liardet 原文 DOI](https://doi.org/10.1090/S0002-9939-1991-1062392-7)
- [Feng–Wen–Wu 作者原文](https://www.math.cuhk.edu.hk/~djfeng/fengpapers/old-papers/FWW_SC.pdf) · [Cabrelli 等 §5](https://mate.dm.uba.ar/~hafg/papers/h-sets.pdf)
- [CLU 作者原文与 Table 1](https://arxiv.org/abs/1805.11904) · [Fan–Liao–Wang–Wu 出版页](https://doi.org/10.1017/S0143385708000138)
- [BLR 原文 Corollary 8](https://arxiv.org/pdf/1710.03596) · [BLR 出版页](https://doi.org/10.1017/S0013091518000585)
- [Moreira 出版页](https://annals.math.princeton.edu/2018/188-1/p03) · [Lima–Moreira 作者预印本](https://arxiv.org/abs/1801.04636) · [Moreira–Erazo–Angelini v3](https://arxiv.org/abs/2511.10328v3)
- 项目原始依据为归档的 Classification.lean、SpectralGap.lean 及复跑公理输出。

## M2 · 旗舰定理与数值区间

- **B1–B4 已写入。** 有限水平的并集为零维，无穷水平满 Lebesgue 测度且维数为一。新加入的测度证明只用 \(\{x:\|Q_jx\|\le m/j\}\) 的测度 \(2m/j\to0\)。摘要和引言按临界标度、全部有限水平、模 4 区间、规定极限的顺序写。第 3、5 项改为直接推论，\(\alpha=0\) 归于 BLR Cor. 8，正权重则限定为论文给出的统一构造与上界。
- **定理 12 的加强。** 在同一标度族 \(g_b(1/Q_n)=b^{-n}\) 中，\(b>2k+1\) 时整个精确水平集的测度为零，\(1<b<2k+1\) 时测度非 σ-有限，唯有临界 \(b=2k+1\) 给出无限而 σ-有限。定理后也将临界速度写成 \(-\log h_k(r)\sim\log(2k+1)\log(1/r)/\log\log(1/r)\)，给出速率严格偏离时的测度结论。与 Moreira–Erazo–Angelini 的比较限定在经典 Lagrange 值为 3 的水平集。
- **C2、C4 已写入。** 现行定理 16 的严格区间为 \((357/512,359/512)\)，宽 \(1/256=0.00390625\)。原初等宽界以严格压力区间替换。CLU 的 \(0.743586\) 属 \(1\bmod3\) 字母集，经 Proposition 2.7 的逐位增大传给 \(1\bmod4\) 字母集。
- **C1、C3 尚有外部步骤。** Bowen 公式、两分支复合后的统一收缩、有限截断和无限尾项都写进正文。内部整数核算可复现，做过同类计算的研究者尚未反馈。代码与日志已备齐，公共仓库待作者许可和归档地址。

从计算目录运行 **python residue_certificate.py**。仅用 Python 3 标准库。程序用 256 个网格单元与正权向量，严格验证完备字母集的负压力和有限子集的正压力。积分处理后半截断项，无需逐一枚举 \(2^{24}\) 个分支。proposals 的浮点运算仅选出整数候选值，每个幂区间端点均以精确整数式验证。日志记录两条相对余量和有理区间。

## M3 · 形式化与复现

**D1 已完成。** 以空的项目构建目录重编全部项目源文件。从本机复用已安装的依赖，为降低并发读取开销以两个线程重跑，9090 个构建任务及后续公理审计均成功退出。另在原环境重跑保存了一套成功的构建、公理审计和附加声明日志。归档保留首轮读依赖时失败的构建日志及后续成功记录。

**D2 已提供锁文件与复现命令。** Lean 为 4.35.0，mathlib 提交为 56a005855ea17e0b0958f73ec801ae140b0a1679。解包后进入 Lean 源码目录，用 PowerShell 7 或支持 && 的 shell 执行 **lake build && lake env lean Audit.lean && lake env lean UnweightedCorrection.lean**。在无依赖环境进行的两次拉取均遇到 GitHub DNS 解析故障。这部分复现仍待可访问上游的环境确认。本机依赖记录了本地改动警告。

**D3、D4 的口径。** Classification、SpectralGap、DimHFinite 的正文条目统一标 Layer A。两项 \(\delta_j\) 输入已由 DeltaSign.lean 中的 Hermite 积分证明替代，定理 1、2、推论 3、5 都没有额外的 \(\delta\) 公理。Lean 核验的结论与纸面证明的临界标度、转移算子说明分别列出。Audit.lean 中某些带日期的历史注释记录的是早期依赖，以当前逐声明公理输出为准。

| 正文 | 复核声明 |
|---|---|
| 定理 1 和 2 | Classification.theorem2_classification、Classification.corollary3_gap |
| 推论 3 和 5 | SpectralGap.spectral_gap、SpectralGap.apprExponent_eq_zero_iff、SpectralGap.levelSet_below_eq_lattice、SpectralGap.dimH_levelSet_below |
| 定理 8 | DimHFinite.dimH_levelSet_finite |
| 两项误差估计 | DeltaSign.deltaSel_tendsto_zero_proved、DeltaSign.abs_deltaSel_lt_proved |

上述声明的本轮公理闭包均仅含 propext、Classical.choice 和 Quot.sound。全项目的审计日志中共有 0 行报告 sorryAx。项目外层同时收录了其他研究用声明，个别声明仍调用各自标注的外部数学输入。

## M4 · 专家复核、作者贡献及发布

E1 的私人复核请求和 E5 的投稿信草稿均见「复核与投稿信草稿」。当前缺独立专家书面反馈、作者最终署名与贡献记录，以及已确认的投稿渠道。arXiv 与期刊提交依清单顺序办理，投稿信草稿留给作者在完成这些条件后签发。

E3 附表的档位可以帮助判断主题匹配，E4 的作者资格和内容来源要求单独适用。数值宽度达到 C 的目标，现行政策核查记录见「期刊政策记录」。稿件已加入 Research assistance 说明，按实际研究贡献填写的正式披露仍需由拟署名作者确认。专家对技术的复核也需要保留独立记录。
