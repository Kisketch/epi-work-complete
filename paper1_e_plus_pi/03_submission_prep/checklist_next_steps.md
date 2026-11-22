# 伴随论文与主论文核查留痕及下一步计划（2026-11-20）

> 遵守 `AGENTS.md` 纪律：严格按诚实五分类法与 Lean 三层公理层级记录；只保留通过构建/核验的关键步骤与实测输出，不记录失败实验或无效代码。

---

## 一、本机工具链清点（实测可用）

| 类别 | 工具 | 实测路径 / 版本 |
|---|---|---|
| LaTeX 编译 | MiKTeX `pdflatex` / `xelatex` / `latexmk` / `biber` | `C:\Users\Lgnatius\AppData\Local\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe` |
| Lean 4 | `lean` / `lake`（`epi_formal/lean-toolchain` 锁定 `v4.35.0`；全局默认 `4.36.0`） | `%USERPROFILE%\.elan\bin\lake.exe` |
| Python 高精度计算 | `.venv\Scripts\python.exe`（Python 3.12.14） | `sympy 1.14.0`、`mpmath 1.3.0` |
| 版本与网络 | `git`、`node`、`uv`；`github.com:443` TCP 可达（`198.18.0.108`） | `C:\Program Files\Git\cmd\git.exe` |

---

## 二、已核实通过的实测记录（分类与公理分层）

### 2.1 Lean 4 形式化（类别：文献核查与复现 / 既有理论机器验证）
- **构建**：`epi_formal` 执行 `lake build`，退出码 `0`（9090 jobs，零错误）。
- **审计**：`lake env lean Audit.lean`，退出码 `0`，导出 `124` 条 `#print axioms` 输出，`sorryAx` 计数 = `0`（日志：`../../lean_audit_verify.log`）。
- **独立反例模块**：`lake env lean ..\paper1_e_plus_pi\04_formalization_audits\UnweightedCorrection.lean`，退出码 `0`，`'UnweightedCorrection.witness'` 仅依赖 `[propext, Classical.choice, Quot.sound]`。
- **mathlib 完整性**：`epi_formal\.lake\packages\mathlib` 下 `git diff --ignore-all-space --stat` 输出为空，确认无代码篡改（仅有 Windows CRLF 行尾提示）。
- **三层公理清单**：
  1. **Lean 基础公理**：`propext`、`Classical.choice`、`Quot.sound`（覆盖 `DimHFinite.dimH_levelSet_finite`、`WeightedFinal.dimH_levelSetα_le`、`QuarterPointFinal.lambda_x0_eq_quarter`、`DeltaSign`、`Classification`、`SpectralGap`、`EscapeReduction` 等）。
  2. **经典白名单公理（3 条）**：`e_transcendental`、`pi_transcendental`、`mu_e_eq_two`。
  3. **项目自加公理**：`0` 条（`deltaSel_tendsto_zero`、`abs_deltaSel_lt`、`meiburg_criterion` 均已证为定理）。

### 2.2 数值与证书验证（类别：有限计算与严格整数认证，非内核证明）
- **定理 16 转移算子整数证书**：`.venv\Scripts\python.exe residue_certificate.py` 退出码 `0`：
  - `lower s=357/512  min relative margin=+0.002922128  exact=7204302042904417931/2465429597500000000000`
  - `upper s=359/512  min relative margin=+0.006596281  exact=65040245891337248463/9860138780000000000000`
  - `Certified: 357/512 < dimension < 359/512; interval width = 1/256`

---

## 三、关键数学步骤人工逐行核验留痕（伴随论文 `Phase2_revised.tex`）

1. **定理 12（临界规范函数 $h_k$，类别：无条件新结果，纸面证明）**
   - 递推恒等式：$d_j = M_{j+1} - A_j M_j - M_{j-1} = A_j u_j + u_{j-1} - u_{j+1}$（因 $Q_{j+1} = A_j Q_j + Q_{j-1}$）。
   - Borel 覆盖与计数：$\Lambda(x)\le k/4 \implies$ 最终 $|d_j|\le k$（$b=2k+1$ 选法），同起点类至多 $b^{n-N}$ 区间，直径 $\le 1/Q_n \implies \mathcal{H}^{h_k}$-cost $\le b^{-N}$；严格子水平 $|d_j|\le k-1$ 贡献趋零。
   - 正性构造：$W_j = d_j Q_j - W_{j-1}$ 与 $|W_j|\le 2k Q_j$ 给出 $|x-M_j/Q_j|\le 4k/Q_{j+1}$，质量分布 $\mu(I)\le 3 b^{N+1} h_k(h)$ 对所有 $1/Q_{n+1}\le h < 1/Q_n$ 成立（$N\le j<n$ 时 $|M_j(x)-M_j(y)| < Q_j/Q_n + 1/4 < 1$ 唯一锁定）。
   - 无穷性反证：利用 $L\bmod 1$ 稠密平移不变性将有限正规范化测度延拓为 $\mathbb{R}/\mathbb{Z}$ 上的旋转不变概率测度（必为 Lebesgue 测度），与定理 8 零 Lebesgue 测度矛盾。

2. **定理 14–15（短窗口几乎处处对数次 vs 发散窗口满维数，类别：无条件新结果，纸面证明）**
   - 定理 14：停时柱 $\tau_j=k(j)+1$ 上条件概率 $\mathbb{P}(a\ge A\mid\mathcal{F}_j)=\frac{q+q'}{Aq+q'}\ge\frac{1}{A}\ge\frac{H_j}{2H_{j+1}}\ge\frac{c_0}{j}$（关键不等式 $A(q+q')\ge Aq+q'$ 对 $A\ge 1, q'\ge 0$ 恒成立）；指数鞅型递推得 $\mathbb{E}e^{-Z_J}\le C J^{-b}$，沿 $J=2^m$ 用 Borel–Cantelli 收口。
   - 定理 15：矩形 $[0.34R, 0.35R]\times[0.12R, 0.13R]$ 内互素点由 Möbius 反演给出 $\gg R^2\gg j^{2\gamma}$ 子柱，尾接 $4$ 跨过 $H_{j+1}$ 且 $4t+v'\in[4T/3, 5T/2]$，质量分布给出 $\dim_H\ge 1-\eta\log\varphi$。

3. **定理 16（模 4 最终周期维数，类别：无条件新结果 + 严格整数认证，纸面证明+代码）**
   - 满射覆盖显式验证：对任意 $x=[0;d_1,d_2,\ldots]\in E$，取 $c_i=(d_i-1)\bmod 4\in\{0,1,2,3\}$，则 $d_i-c_i=4\lfloor(d_i-1)/4\rfloor+1\in\mathcal{A}=\{1,5,9,\ldots\}$，且 $(c_i)$ 随 $(d_i\bmod 4)$ 最终周期。
   - 统一 Lipschitz 常数 $40/3$：首异位 $a<b$（$b-a\ge 4$）处尾距比 $\le \frac{b-a+1}{b-a-1}\frac{(a+1)b}{a(b+1)}<\frac{5}{3}\cdot 2=\frac{10}{3}$，恢复共同前缀因子 $\le 4$ 得 $40/3$。
   - 两字母分支导数 $|(f_a\circ f_b)'(x)|=(ab+ax+1)^{-2}\le 1/4$ 满足 CLU §2 Theorem 2.3 压缩条件。

---

## 四、本轮已修复的论文问题与 PDF 同步状态

1. **伴随论文（12 页，已重编译 EXIT 0）**：
   - 修正 `MEA`（[arXiv:2511.10328v3](../../verification/reference_pdfs/MEA_2511_10328v3.pdf)）错题（`dimension` $\to$ `measure`）；
   - 补齐 `LimaMoreira` 已刊卷页 *Ann. Inst. H. Poincaré C* 38 (2021), 1429–1459；
   - `FWW` 原 PDF 返回 404，按 A3/引用纪律移除未核的 `Theorem 2.1` 编号；
   - 摘要、Theorem 10 与 §10 更新为 `WeightedFinal.dimH_levelSetα_le`（Layer A 全覆盖机器验证）及 `QuarterPointFinal.lambda_x0_eq_quarter`；
   - 定理 16 补全 $c_i=(d_i-1)\bmod 4$ 满射步。
2. **主论文（42 页，已重编译 EXIT 0）**：
   - 清理全部 6 处弱来源/媒体引用（`KepuTrans`、`KepuAlgebraic`、`SchanuelWiki`、`MathWorldMeasure`、`MathWorldFlint`、媒体版 `MPT2019`），全部替换为已核一次文献（`Hermite1873`、`ZZ2020`、`Ax1971`、`MPT2019`、`BakkerTsimerman2019`、`Baker`、`Tijdemann1971`）；
   - 更新日期与 Appendix A/B 审计和本地复现说明。
3. **本地 PDF 全部同步一致**：
   - 主论文：`paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.pdf`（同名旧版在 `06_historical_versions/archive_snapshots/papers_old/paper1_old.pdf`）SHA256 一致；
   - 伴随论文：`paper1_e_plus_pi/02_companion_paper/Phase2_revised.pdf`；论文二当前版 `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.pdf`；旧版归档至 `paper2_spectral_gap_dimension/historical_versions/`（2026-11-21 整理后路径更新，内容与 SHA256 未变）。

---

## 五、下一步研究与投稿计划（分类推进）

| 优先级 | 路线 | 目标与类别 | 可证伪检验 / 验收标准 |
|---|---|---|---|
| **P1** | **伴随论文 D2 洁净复现** | 文献核查与复现 / 工程 | 在无本地缓存（或 `lake clean` 独立目录）下利用当前可达的 GitHub 网络实测 `lake build && lake env lean Audit.lean && lake env lean UnweightedCorrection.lean` 并归档日志 |
| **P2** | **伴随论文 E1/E3–E5** | 投稿事务（非证明） | 人类作者逐行核验纸面证明并确定署名与 AI 贡献记录；发私人复核信予 V. Chousionis / D. Leykekhman；依 AI 政策在 *J. Number Theory* / *Acta Arith.* / *Experimental Math.* / *Proc. Edinburgh Math. Soc.* 选刊后先挂 arXiv |
| **P3** | **主论文对照模型 $6-e$**（任务 B） | 独立模型问题（等价/边界测试） | 用高精度 Python 计算检验 $c_\varphi(6-e)$ 是否取到 $1-2/\sqrt{5}$，再尝试补全前周期首次失配段下界以闭合等号或构造更小极限 |
| **P4** | **主论文 §8 窗定理形式化与 Perron/Stambul 边界核查**（任务 C） | 文献核查与复现 + 形式化 | 核对 Perron §33 / Stambul (1997) 确定显式周期 $2B^2, 2B|C|$ 与阈值 $j>B^2$ 的新颖边界；在 Lean 补入 gcd 约分向量证明链 |
| **P5** | **真实 $\pi$ 的专属解析下界**（任务 A） | 开放问题（$e+\pi$ 无理性） | 仅在出现作用于真实 $\pi$ 指定尺度（$H_j$ 或 $E_\varphi$）的新解析输入时推进；不重复通用递推/非有效 $\mu(\pi)$ 空转 |
