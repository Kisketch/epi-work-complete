"""prereq 背景复述保真度升级（2026-11-23）：补 g_beta 句 + liminf 三态明细。

依据：与 sec-gauge-core.tex 原文逐项对账。
- thm:gauge 原文 L12-20 含 g_beta 两向结论，旧复述遗漏 -> 补一句。
- cor:liminf-gauges 原文 L371-384 为三态分类，旧复述只一句话 -> 展开三态。
两处改动同步应用于 prereq-2B.tex 与 prereq-2C.tex（文本一致）。
"""

FILES = [
    r"paper2_spectral_gap_dimension/split/src_sections/prereq-2B.tex",
    r"paper2_spectral_gap_dimension/split/src_sections/prereq-2C.tex",
]

G_OLD = """$\\{\\Lam<k/4\\}$ is $\\mathcal{H}^{h_k}$-null.
\\end{theorem}"""
G_NEW = """$\\{\\Lam<k/4\\}$ is $\\mathcal{H}^{h_k}$-null.
In the family $g_\\beta(1/Q_n)=\\beta^{-n}$ the level is null for
$\\beta>2k+1$ and non-$\\sigma$-finite for $1<\\beta<2k+1$.
\\end{theorem}"""

C_OLD = """Every nondecreasing gauge is classified by
$\\liminf_n(2k+1)^n g(1/Q_n)$ (resp.\\ $\\liminf_n2^n g(1/Q_n)$ for the
unsigned exact-limit set)."""
C_NEW = """Let $\\rho_b(g)=\\liminf_n b^n g(1/Q_n)$ with $b=2k+1$ for
$S_k$ and $b=2$ for the unsigned exact limits.
The set is $\\mathcal{H}^g$-null if $\\rho_b(g)=0$;
$\\sigma$-finite with infinite measure in every nonempty open set if
$0<\\rho_b(g)<\\infty$; non-$\\sigma$-finite in every nonempty open set
if $\\rho_b(g)=\\infty$. For $b=2k+1$ nullity extends to
$\\{\\Lam\\le k/4\\}$."""

for p in FILES:
    t = open(p, encoding="utf-8").read()
    assert t.count(G_OLD) == 1, p
    assert t.count(C_OLD) == 1, p
    t = t.replace(G_OLD, G_NEW).replace(C_OLD, C_NEW)
    open(p, "w", encoding="utf-8", newline="").write(t)
    print("patched", p)
