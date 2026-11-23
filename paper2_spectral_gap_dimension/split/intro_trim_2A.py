"""2A 引言机械裁剪：从 intro-shared.tex 删除轨外句子，生成 intro-2A.tex。

删除依据（ explorer 句级表，2A 列=删）：
  D1 S8/S9 : thm:finite-state-tail 两句（Perron 根）
  D2 S11/S12: poly 推广 + growing-rec 整块
  D3 S17    : Finally 起的窗口/残差整块
其余一字不动（含 S5/S16 改写暂缓，原样保留）。
"""

SRC = "paper2_spectral_gap_dimension/split/src_sections/intro-shared.tex"
DST = "paper2_spectral_gap_dimension/split/src_sections/intro-2A.tex"

t = open(SRC, encoding="utf-8").read()
n0 = len(t)

d1_start = " Theorem~\\ref{thm:finite-state-tail} shows how this"
d1_end = "can revisit an extreme defect infinitely often.\n"
i = t.index(d1_start)
j = t.index(d1_end) + len(d1_end)
t = t[:i] + t[j:]

d2_start = " Theorems~\\ref{thm:general-rec}"
d2_end = "rational sublattice $\\frac{1}{g}\\Z$.\n"
i = t.index(d2_start)
j = t.index(d2_end) + len(d2_end)
t = t[:i] + t[j:]

d3_start = " Finally, in\nSection~\\ref{sec:windows-residues}"
d3_end = "its metallic-continuant generalizations $C_r=\\sum_{k=1}^\\infty 1/q_k(r)$.\n"
i = t.index(d3_start)
j = t.index(d3_end) + len(d3_end)
t = t[:i] + t[j:]

# D4 S28/S29: P11 整块（general irrational 起至 digit sets 句末）
d4_start = "For a general irrational $\\alpha$ whose partial quotients tend to infinity, we\nFirst treat"
d4_end = "asymptotic dimension constant of modular continued-fraction digit sets).\n"
i = t.index(d4_start)
j = t.index(d4_end) + len(d4_end)
t = t[:i] + t[j:]

# D5 S30: 贡献清单改写为 2A-only
d5_old = """The main new contributions are the complete spectrum discretization and
three-way positive-level splitting (Theorems~\\ref{thm:full-spectrum},
\\ref{thm:trichotomy}, \\ref{thm:general-rec}--\\ref{thm:poly-phase-transition},
and~\\ref{thm:growing-rec-spectrum}--\\ref{thm:growing-rec-dim-phase}), the critical gauge theorems
(Theorem~\\ref{thm:gauge} and Corollary~\\ref{cor:exact-gauge}), the machine-checked
dimension-zero and subcritical dimension theorems (Theorems~\\ref{thm:finite},
\\ref{thm:upper}, and~\\ref{conj:weight}), and the continued-fraction window and
residue theorems (Theorems~\\ref{thm:windows}--\\ref{thm:residues-asymptotic})."""
d5_new = """The main new contributions are the complete spectrum discretization and
three-way positive-level splitting (Theorems~\\ref{thm:full-spectrum} and~\\ref{thm:trichotomy}),
the critical gauge theorems (Theorem~\\ref{thm:gauge} and Corollary~\\ref{cor:exact-gauge}),
and the machine-checked dimension-zero and subcritical dimension theorems
(Theorems~\\ref{thm:finite}, \\ref{thm:upper}, and~\\ref{conj:weight})."""
assert d5_old in t
t = t.replace(d5_old, d5_new)

while "\n\n\n" in t:
    t = t.replace("\n\n\n", "\n\n")

open(DST, "w", encoding="utf-8", newline="").write(t)
print("orig chars:", n0)
print("new chars:", len(t), "removed:", n0 - len(t))
print("new lines:", t.count("\n") + 1)
