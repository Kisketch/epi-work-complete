"""2B 引言改写：从 intro-shared.tex 确定性生成 intro-2B.tex。

依据 explorer 句级裁剪表（2B 列）：
留：S11/S12（poly+growing 综述）、S19 原型句、S20（eq:rec）、S28（P11 前半）。
改：S1（主语换 A_j）、S4（poly 规范单句）、S10（多项式/growing 版三分法）、
    S18（跨篇引用 2A 基座）、S24（Hensley 两句）、S25（归一化一句）、S30（2B-only 贡献）。
删：S2/S3/S5/S6/S7/S8/S9/S13–S17/S21/S22/S23/S26/S27/S29/S31/S32/S33。
新写句子标注 [2B-NEW]，其余逐字源自原稿。
"""

SRC = "paper2_spectral_gap_dimension/split/src_sections/intro-shared.tex"
DST = "paper2_spectral_gap_dimension/split/src_sections/intro-2B.tex"

t = open(SRC, encoding="utf-8").read()
n0 = len(t)


def rep(start, end, new, tag):
    global t
    i = t.index(start)
    j = t.index(end) + len(end)
    t = t[:i] + new + t[j:]
    print(tag, "removed:", j - i, "added:", len(new))


# S1+S2+S3 -> OPEN（L4-17 整块）
rep(
    "This article studies the metric theory",
    "Corollary~\\ref{thm:sub}).\n",
    "[2B-NEW-OPEN] This article develops the metric theory of Diophantine\n"
    "approximation along general integer three-term recurrences\n"
    "$Q_{j+1}=A_jQ_j+Q_{j-1}$ with $A_j\\ge2$ and $A_j\\to\\infty$.\n"
    "The selected convergent denominators of $\\ee$ ($A_j=4j+2$) are the\n"
    "motivating prototype.\n",
    "OPEN",
)

# S4+S5+S6 -> S4'（L19-33 整块）
rep(
    "Our main metric result at the critical weight, Theorem~\\ref{thm:gauge},",
    "measure of $\\{\\Lam=k/4\\}$ is infinite in every nonempty open arc.\n",
    "[2B-NEW-S4] At each positive level the critical gauge has base $2k+1$\n"
    "with $1/r$-scaled logarithmic order\n"
    "(Theorem~\\ref{thm:poly-gauge-trichotomy}), and the exact gauge of\n"
    "Corollary~\\ref{cor:poly-exact-gauge} is sharp.\n",
    "S4",
)

# S7+S8+S9 删除（L34-39）
rep(
    "Corollary~\\ref{cor:liminf-gauges} classifies every nondecreasing gauge",
    "can revisit an extreme defect infinitely often.\n",
    "",
    "S7-S9",
)

# S10 -> S10'（L40-46：trichotomy 句，句号结尾，后接 poly 块保留）
rep(
    "Furthermore, Theorem~\\ref{thm:trichotomy} establishes a sharp three-way",
    "single countable $L$-coset).",
    "[2B-NEW-S10] The positive-level three-way splitting persists over general\n"
    "$(r,c,d)$ and growing $A_j$: limsup level, universal binary exact limits,\n"
    "and single-coset signed limits with respect to the intrinsic lattice\n"
    "$L^{(r,c,d)}$ (resp.\\ $L_G$).",
    "S10",
)

# S13-S17 删除（L65-89：finite/weights/窗口残差整块）
rep(
    "On the coarse scale of Hausdorff dimension, Theorem~\\ref{thm:finite} shows that",
    "its metallic-continuant generalizations $C_r=\\sum_{k=1}^\\infty 1/q_k(r)$.\n",
    "",
    "S13-S17",
)

# S18 -> S18'（L91-93）
rep(
    "These results build on the zero-level classification and initial spectral gap",
    "project on the (open) irrationality of $e+\\pi$ \\cite{Phase1}.\n",
    "[2B-NEW-S18] The zero-level classification and initial gap for the $e$\n"
    "prototype are taken as base from the companion core paper (2A); the work\n"
    "below is over general $(r,c,d)$ and growing $A_j$.\n",
    "S18",
)

# S21-S23 删除（L104-111：Lam 定义与 L）
rep(
    "Write $\\|y\\|=\\dist(y,\\Z)$ and define",
    "Let $L:=\\Z+\\Z\\frac{\\ee+1}{2}$, a countable dense subgroup of $\\R$.\n",
    "",
    "S21-S23",
)

# S24+S25+bullets -> S24'+S25'（L115-160 整块）
rep(
    "The \\emph{phenomenon} (a spectral gap plus zero-dimensional sub-threshold level\nsets) is classical:",
    "\\end{itemize}\n",
    "[2B-NEW-S24] On the continued-fraction side this continues the\n"
    "infinite-alphabet dimension theory of Hensley and Jenkinson--Pollicott for\n"
    "sets defined by digit constraints.\n"
    "[2B-NEW-S25] As in Kraaikamp--Liardet \\cite{KL}, the constants $1/4$ and\n"
    "$1/2$ differ only by normalization; Theorem~\\ref{thm:growing-rec-spectrum}(i)\n"
    "matches their error normalization across all growing quotients.\n",
    "S24-S25",
)

# S29 删除（L178-190：F_{m,r}/CLU/渐近整块）
rep(
    "For the modular continued-fraction alphabets",
    "asymptotic dimension constant of modular continued-fraction digit sets).\n",
    "",
    "S29",
)

# S30 -> S30'（贡献清单）
rep(
    "Accordingly, we",
    "residue theorems (Theorems~\\ref{thm:windows}--\\ref{thm:residues-asymptotic}).",
    "[2B-NEW-S30] The main new contributions are the complete discretization and\n"
    "exact gauges for $(cj^r+d)$ recurrences\n"
    "(Theorems~\\ref{thm:general-rec}--\\ref{thm:poly-phase-transition} and\n"
    "Corollary~\\ref{cor:poly-exact-gauge}) and the unified growing-quotient phase\n"
    "diagram (Theorems~\\ref{thm:growing-rec-spectrum}\n"
    "and~\\ref{thm:growing-rec-dim-phase},\n"
    "Corollary~\\ref{cor:growing-rec-three-regimes}).",
    "S30",
)

# S31-S33 删除（L202-236：BLR/CMMS/四特征整块）
rep(
    "For the selected sequence $(Q_j)$, Corollary~8 of Bugeaud, Liao and Rams",
    "whereas without the weight the branching grows linearly and the unweighted\n"
    "zero-set $\\{x:\\|Q_jx\\|\\to0\\}$ has full dimension $1$, while the weighted\n"
    "zero-set $\\{x:j\\|Q_jx\\|\\to0\\}$ equals the countable group $L$.\n",
    "",
    "S31-S33",
)

# S28 删除（与 S11/S12 重复的 poly→growing 复述段；KL 恒等式已由 S25' 覆盖）
rep(
    "For a general irrational $\\alpha$ whose partial quotients tend to infinity, we\nFirst treat",
    "collapse from $L_G$ to $\\frac{1}{g}\\Z$ across $\\tau_{\\mathrm{crit}}=1+1/\\gamma_{\\sup}$.\n",
    "",
    "S28-dup",
)

while "\n\n\n" in t:
    t = t.replace("\n\n\n", "\n\n")

open(DST, "w", encoding="utf-8", newline="").write(t)
print("orig chars:", n0)
print("new chars:", len(t), "removed:", n0 - len(t))
print("new lines:", t.count("\n") + 1)
