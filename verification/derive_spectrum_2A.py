"""派生 sec-spectrum-2A.tex：仅改写审计归属段（方案A），其余逐字节同原切片。"""
SRC = "paper2_spectral_gap_dimension/split/src_sections/sec-spectrum.tex"
DST = "paper2_spectral_gap_dimension/split/src_sections/sec-spectrum-2A.tex"
t = open(SRC, encoding="utf-8").read()

old = """All of these modules---along with
\\texttt{Gauge\\allowbreak Liminf\\allowbreak Complete.lean},
\\texttt{Finite\\allowbreak State\\allowbreak Gauge.lean},
\\texttt{Finite\\allowbreak State\\allowbreak Positive.lean},
\\texttt{Finite\\allowbreak State\\allowbreak Complete.lean},
\\texttt{Window\\allowbreak Short\\allowbreak AeRealize.lean},
\\texttt{Residue\\allowbreak ModGeneral.lean},
\\texttt{Transfer\\allowbreak Operator\\allowbreak Dim.lean}, and
\\texttt{Trichotomy\\allowbreak And\\allowbreak Poly\\allowbreak Extension.lean}
(which completes Theorem~\\ref{thm:trichotomy}(iii) and Section~\\ref{sec:poly-rec})---are
audited together in \\texttt{Audit.lean} ($872$ declarations across $131$ files,
$9176$ build jobs) with zero \\texttt{sorryAx} and only the three Lean base axioms."""

new = """All of these modules---along with
\\texttt{Gauge\\allowbreak Liminf\\allowbreak Complete.lean} and the part-(iii)
portion of \\texttt{Trichotomy\\allowbreak And\\allowbreak Poly\\allowbreak Extension.lean},
which completes Theorem~\\ref{thm:trichotomy}(iii) (its general $(cj^r+d)$ half
is treated in the companion general-theory paper)---are audited together in
\\texttt{Audit.lean} with zero \\texttt{sorryAx} and only the three Lean base
axioms; the full-library audit now spans $937$ declarations across $134$ files."""

assert t.count(old) == 1
t = t.replace(old, new)
open(DST, "w", encoding="utf-8", newline="").write(t)
print("wrote", DST)
