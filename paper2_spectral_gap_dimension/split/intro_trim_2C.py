"""2C 引言改写 v2：按行号 deterministic 生成 intro-2C.tex（源文件不动）。

行号依据（intro-shared.tex，共 237 行，已逐行验）：
 L1-3   留（section 头）
 L4-17  S1-S3 -> OPEN
 L18    留（空行，占位折叠）
 L19-33 S4-S6 删
 L34-39 S7-S9 留 + NOTATION
 L40-75 S10-S16 删
 L76    改写为独立起句（原句前半删，保留 Finally 起的窗口段）
 L77-89 S17 留
 L90    留
 L91-93 S18 删
 L94-96 留（Setup 节头）
 L97-110 Setup 内容留（S19/S20）
 L111   L 定义删
 L112-114 留（空行 + Relation 节头）
 L115-177 S24-S28 删（含 KL/子弹/P11 前半）
 L178-190 S29 留
 L191-200 S30 -> 2C-only
 L201   留
 L202-236 S31-S33 删
 L237   留
新写句子标注 [2C-NEW]。
"""

SRC = "paper2_spectral_gap_dimension/split/src_sections/intro-shared.tex"
DST = "paper2_spectral_gap_dimension/split/src_sections/intro-2C.tex"

lines = open(SRC, encoding="utf-8").read().splitlines(keepends=True)
assert len(lines) == 237, len(lines)
L = lambda i: lines[i - 1]  # 1-based

assert L(4).startswith("This article studies the metric theory")
assert L(17).rstrip().endswith("Corollary~\\ref{thm:sub}).")
assert L(19).startswith("Our main metric result")
assert L(33).rstrip().endswith("in every nonempty open arc.")
assert L(34).startswith("Corollary~\\ref{cor:liminf-gauges}")
assert L(39).rstrip().endswith("infinitely often.")
assert L(40).startswith("Furthermore, Theorem~\\ref{thm:trichotomy}")
assert L(75).rstrip().endswith("\\cite{BLR}, and")
assert L(76).startswith("both bounds for $0\\le\\alpha<1$")
assert L(77).startswith("Section~\\ref{sec:windows-residues}")
assert L(89).rstrip().endswith("1/q_k(r)$.")
assert L(91).startswith("These results build on the zero-level")
assert L(93).rstrip().endswith("\\cite{Phase1}.")
assert L(95).startswith("\\subsection{Setup}")
assert L(97).startswith("The continued fraction of $\\ee$")
assert L(111).startswith("Let $L:=")
assert L(113).startswith("\\subsection{Relation to prior work}")
assert L(115).startswith("The \\emph{phenomenon}")
assert L(160).rstrip() == "\\end{itemize}"
assert L(161).startswith("For a general irrational")
assert L(177).rstrip().endswith("\\gamma_{\\sup}$.")
assert L(178).startswith("For the modular continued-fraction alphabets")
assert L(190).rstrip().endswith("digit sets).")
assert L(191).startswith("Accordingly, we")
assert L(200).rstrip().endswith("--\\ref{thm:residues-asymptotic}).")
assert L(202).startswith("For the selected sequence $(Q_j)$, Corollary~8")
assert L(236).rstrip().endswith("countable group $L$.")

OPEN = (
    "[2C-NEW-OPEN] This article determines the dimensions and almost-sure\n"
    "frequencies of Hermite continued-fraction window constraints, the Hausdorff\n"
    "dimensions of modular digit-residue sets, and the finite-state tail gauge\n"
    "theory, along the selected convergent denominators of $e$.\n"
)
NOTATION = (
    "[2C-NEW-NOT] We use the notation of the core paper (2A):\n"
    "$S_k=\\{x\\in\\R/\\Z:\\Lambda(x)=k/4\\}$ for the exact levels and $d_j(x)$\n"
    "for the consecutive-defect sequence; proofs of the quoted gauge results\n"
    "are in 2A.\n"
)
L76_NEW = "In Section~\\ref{sec:windows-residues}, Theorems~\\ref{thm:windows}--\\ref{thm:no-short-dim}\n"
S30_NEW = (
    "[2C-NEW-S30] The main new contributions are the window dimension and\n"
    "short-window laws (Theorems~\\ref{thm:windows}--\\ref{thm:no-short-dim}),\n"
    "the residue dimensions and asymptotics (Theorems~\\ref{thm:residues},\n"
    "~\\ref{thm:residues-general} and~\\ref{thm:residues-asymptotic} with\n"
    "Tables~\\ref{tab:residues-general} and~\\ref{tab:residues-asymptotic}), and\n"
    "the finite-state tail theorem (Theorem~\\ref{thm:finite-state-tail}).\n"
)

out = []
out += lines[0:3]          # L1-3
out.append(OPEN)           # L4-17 replaced
out.append(lines[17])      # L18 blank
# L19-33 dropped
out += lines[33:39]        # L34-39
out.append(NOTATION)       # after L39
# L40-75 dropped
out.append(L76_NEW)        # L76 rewritten
out += lines[76:89]        # L77-89
out.append(lines[89])      # L90 blank
# L91-93 dropped
out.append(lines[93])      # L94 blank
out += lines[94:96]        # L95-96
out += lines[96:110]       # L97-110
# L111 dropped
out.append(lines[111])     # L112 blank
out += lines[112:114]      # L113-114 header
# L115-177 dropped
out += lines[177:190]      # L178-190 S29
out.append(S30_NEW)        # L191-200 replaced
out.append(lines[200])     # L201 blank
# L202-236 dropped
out.append(lines[236])     # L237

text = "".join(out)
while "\n\n\n" in text:
    text = text.replace("\n\n\n", "\n\n")

open(DST, "w", encoding="utf-8", newline="").write(text)
print("new lines:", text.count("\n") + 1)
