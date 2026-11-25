# Paper 2D 独立定理论文：临界标度修复、超临界精确主导常数与稀疏字母表尾相变（2026-11-25）

> **定位声明**：本目录为 Paper 2 系列的独立衍生定理论文（代号 **Paper 2D**），系统修复并大幅推进了历史实验稿 [`../drafts_v3_critical_scaling/sec-critical-scaling.tex`](../drafts_v3_critical_scaling/sec-critical-scaling.tex) 中的 7 处数学缺陷，**无条件证明了此前被标为“未证猜想”的超临界精确主导常数定理**，并证伪了旧启发式常数与朴素无限字母表 $\ge 1/2$ 地板猜想。
>
> **SSOT 隔离原则**：本目录完全独立于 Paper 2 主稿的 11 切片真源（[`../split/src_sections/slice_index.csv`](../split/src_sections/slice_index.csv) 与 [`../paper2_spectral_gap_dimension.tex`](../paper2_spectral_gap_dimension.tex)），不改动主稿与既有三轨；历史旧实验稿 `drafts_v3_critical_scaling/` 原样保留供学者对照审阅。**遵循 [`../../AGENTS.md`](../../AGENTS.md)：本论文不解决 $e+\pi$ 无理性问题。**

---

## 一、核心数学成果一览（遵循 `AGENTS.md` 五分法）

| 编号与结果 | 类别 | 核查状态 | 与旧稿 / 已有文献关系 |
| :--- | :--- | :--- | :--- |
| `lem:pole`（$\Omega=\{\|z-1\|<5/4\}$ 上自含 Perron–Frobenius 与极点分解） | 1 / 5（经典解析转移算子极点分解的自含初等证明） | 纸面完整自含证明（未入 Lean 内核） | 彻底消除旧稿 `sec-critical-scaling.tex` 在复全纯空间 $A(\Omega)$ 上定义实非负锥 $K$ 的致命谬误，并修复 $n=0$ 重复计数、$O((\theta\rho)^n)$ 与 $A(p)$ 跨 $p_0$ 解析域问题；同步修正旧书目 `Mayer1991` 误引为 *ETDS* 的错误（实为 *CMP* 130 (1990), 311–333） |
| `lem:resolvent-uniform`、`lem:master`（三区统一主方程，$m\ge 340\Sigma$） | 1 无条件结果（依赖仓库无 Bowen 转移算子判据） | 纸面完整证明（依赖 `TransferOperatorDim.lean` 已核判据） | 修复旧稿未选截断项数 $N(m,s)$、超临界 $h(1)$ 上界缺失 $(1-s_0)^{-1}$ 及错误假设 $\varepsilon_0\log m\to0$ 的漏洞，证得主方程在次临界、临界、超临界三区一致成立（绝对常数 $C_0=4+48\zeta(2), C_1=172$） |
| **`thm:supercritical-exact`（超临界精确主导常数）**：$\dim_{\mathrm H}F_{m,S,B}-s_0(S)=\frac{d\kappa(S)\zeta(2s_0(S))}{2}m^{-2s_0(S)}(1+O_{S,B}(m^{-1}))$ | **1 无条件新结果**（已知扰动框架下的显式精确渐近公式） | 纸面完整证明 + 30 位 Chebyshev 配置法佐证（$n=44$ vs $48$ 差 $<10^{-32}$） | **实质推进 Paper 2 `thm:multi-residue-asymptotic`(v) 的 $\Theta(m^{-2s_0})$ 双向速率至精确主导常数与 $O(m^{-1})$ 余项**；同时证伪旧启发式常数 $\frac{d\kappa}{2(2s_0-1)}$（旧稿误把 $2s_0>1$ 处的 $\zeta(2s_0)$ 截断为 $1/(2s_0-1)$ 并误判主方程失效） |
| `thm:critical-scaling` & `cor:critical-exp`（临界窗联合标度极限与固定 $S$ 二阶对数修正） | 1 无条件结果（变序列带显式一致假设） | 纸面完整证明 + SymPy 二阶符号校验 | 补齐旧稿缺失的变序列假设（$\Sigma_k/m_k\to0$、$\gamma_k\log m_k\to0$、$\gamma_k=\sqrt{d_k\kappa_k/m_k}$ 归一化与极点余项一致占优），并在固定临界集 $s_0(S)=1/2$ 时新增精确二阶项 $-\frac{d\kappa(S)\log m}{4m}+O_{S,B}(m^{-1})$（明确标注精确满足 $s_0(S)=1/2$ 的有限整数集存在性仍开放） |
| **`prop:sparse-tail-phase`（稀疏字母表反例与尾收敛横坐标相变）** | 1（窄，无 Bowen 6 行新证）+ 5（与 Good / MU96 / DFSU Prop. 9.3 对照） | 纸面完整证明 + 50 位尾和校验 | 精确澄清 $A_{k_0}=\{2^{2^k}:k\ge k_0\}$ 满足 $0<\dim_{\mathrm H}E_{A_{k_0}}\le 2^{-(k_0+1)}<1/2$（证伪朴素无限字母表 $\ge 1/2$ 猜想，同时纠正“$\dim_{\mathrm H}E_{\{2^{2^k}\}}=0$”的不准确表述；给出 $\lim_{k_0\to\infty}\dim_{\mathrm H}E_{A_{k_0}}=0$ 与逃逸集维数 $0$）及一般扰动尾相变 $\lim_{M\to\infty}\dim_{\mathrm H}E_{S\cup(T\cap[M,\infty))}=\max(\theta(T),s_0(S))$ |

---

## 二、目录文件与复现验收命令

- [`paper2D_critical_supercritical_exact.tex`](paper2D_critical_supercritical_exact.tex)：独立成篇 LaTeX 源码（保留 3 项 `% TODO before submission` 人类门禁占位符；DOI 零 `\allowbreak`）。
- [`paper2D_critical_supercritical_exact.pdf`](paper2D_critical_supercritical_exact.pdf)：3 遍 `pdflatex -interaction=nonstopmode` 洁净编译成稿。
- [`paper2D_critical_supercritical_exact.log`](paper2D_critical_supercritical_exact.log)：最终编译日志（0 Error / 0 Undefined / 0 Overfull `\hbox`）。
- 配套数值脚本与输出：[`../../verification/verify_supercritical_exact_constant_20261125.py`](../../verification/verify_supercritical_exact_constant_20261125.py) / [`.log`](../../verification/verify_supercritical_exact_constant_20261125.log) / [`.json`](../../verification/verify_supercritical_exact_constant_20261125.json)。

```powershell
# 1. 重跑 30 位超临界常数与 50 位稀疏字母表校验
py verification\verify_supercritical_exact_constant_20261125.py

# 2. 文献 DOI/arXiv/Retraction 自动核查
py .agents\skills\mathodology-evidence-search\scripts\verify_refs.py paper2_spectral_gap_dimension\spinoff_critical_and_supercritical_exact_20261125\paper2D_critical_supercritical_exact.tex

# 3. 三遍洁净编译
Set-Location paper2_spectral_gap_dimension\spinoff_critical_and_supercritical_exact_20261125
pdflatex -interaction=nonstopmode paper2D_critical_supercritical_exact.tex
pdflatex -interaction=nonstopmode paper2D_critical_supercritical_exact.tex
pdflatex -interaction=nonstopmode paper2D_critical_supercritical_exact.tex
```
