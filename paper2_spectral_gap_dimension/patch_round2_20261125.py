"""Deterministic Round-2 SSOT integration patch for Paper 2 & Split Tracks (2026-11-25).

Updates:
1. sec-windows.tex (tab:residues-general caption, proof tail, and rem:residue-kernel):
   Records ResidueCertStrictOpen.lean (22 declarations in AuditResidueCertStrictOpen.lean),
   discharging the open-interval strictness dependency on Bowen's pressure formalism (R1)
   for all 20 inequalities in Table tab:residues-general directly on base axioms.
2. sec-gauge.tex and sec-finstate.tex (Lean status of sec:finite-state-tail):
   Records PerronFrobenius.lean (13 declarations in AuditPerronFrobenius.lean),
   eliminating the external finite-dimensional Perron-Frobenius eigenvector hypothesis (R3)
   via a Brouwer-free Collatz-Wielandt minimax proof on base axioms only.
3. sec-resasymp.tex (Lean status of sec:windows-residues):
   Records ResidueCertStrictOpen.lean (22), plus companion standalone Papers 2D
   (GeneralAlphabetFloor.lean [15], SupercriticalConstant.lean [6], MuEEqTwo.lean [9])
   and 2E (FullConvergentSpectrum.lean [40], PerronFrobenius.lean [13]).
4. sec-preface.tex, frontmatter.tex, and frontmatter-2C.tex (abstracts):
   Updates Lean verification summary so R1 and R3 are no longer listed outside the kernel,
   reflecting 937 core declarations (Audit.lean) + 156 standalone audit declarations across
   8 standalone audit files spanning 356 Lean files in epi_formal/.
5. sec-verification.tex:
   Updates total Lean file count (356), lists all 8 standalone audit files (156 declarations),
   and removes R1 and R3 from the out-of-kernel exceptions list.
6. Recomputes split/src_sections/slice_index.csv and reassembles paper2_spectral_gap_dimension.tex
   byte-for-byte.
"""

from __future__ import annotations

import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SL = ROOT / "split" / "src_sections"
SLICE_CSV = SL / "slice_index.csv"
MAIN_TEX = ROOT / "paper2_spectral_gap_dimension.tex"

ORDER = [
    "sec-preface.tex",
    "sec-class.tex",
    "sec-spectrum.tex",
    "sec-finite.tex",
    "sec-weights.tex",
    "sec-gauge.tex",
    "sec-growing.tex",
    "sec-windows.tex",
    "sec-resasymp.tex",
    "sec-num.tex",
    "sec-verification.tex",
]


def to_crlf(s: str) -> str:
    return s.replace("\r\n", "\n").replace("\n", "\r\n")


def replace_once(path: Path, old: str, new: str, *, label: str) -> None:
    txt = path.read_bytes().decode("utf-8")
    old_c = to_crlf(old)
    new_c = to_crlf(new)
    cnt = txt.count(old_c)
    if cnt != 1:
        raise AssertionError(f"{path.name} [{label}]: expected 1 match, found {cnt}")
    path.write_bytes(txt.replace(old_c, new_c, 1).encode("utf-8"))


def patch_windows() -> None:
    p = SL / "sec-windows.tex"
    replace_once(
        p,
        "and, for the closed brackets, by the Lean kernel\n(Remark~\\ref{rem:residue-kernel}).",
        "and, for both closed brackets and strict open inequalities, by the Lean kernel\n"
        "(Remark~\\ref{rem:residue-kernel}).",
        label="windows-proof-strict",
    )
    replace_once(
        p,
        "The closed brackets are kernel-checked in Lean~4 (Remark~\\ref{rem:residue-kernel}).",
        "All $20$ strict open bounds in Table~\\ref{tab:residues-general} are kernel-checked "
        "in Lean~4 on base axioms only (Remark~\\ref{rem:residue-kernel}).",
        label="windows-table-caption",
    )
    replace_once(
        p,
        "\\texttt{EpiFormal/\\allowbreak ResidueCertTable.lean}. Strictness of the brackets\n"
        "(open intervals) uses the positive margins and the pressure argument of\n"
        "Theorem~\\ref{thm:residues}, which is not formalised.\n"
        "\\end{remark}",
        "\\texttt{EpiFormal/\\allowbreak ResidueCertTable.lean} ($27$ declarations audited "
        "in \\texttt{AuditResidueCert.lean}). Moreover, "
        "\\texttt{EpiFormal/\\allowbreak ResidueCertStrictOpen.lean} ($22$ declarations "
        "audited in \\texttt{AuditResidueCertStrictOpen.lean}, base axioms only, zero "
        "\\texttt{sorryAx}, and zero Python recomputation) upgrades every entry of "
        "Table~\\ref{tab:residues-general} directly inside Lean~4 from the positive "
        "certificate step margins via monotone operator comparison "
        "(\\texttt{dimH\\_lt\\_of\\_certU} and \\texttt{lt\\_dimH\\_of\\_certL}), establishing "
        "all $20$ strict open inequalities $\\mathrm{lower}<\\dimH F_{m,r}<\\mathrm{upper}$ "
        "($m\\in\\{2,3,4,5,6\\}$, $r\\in\\{1,m\\}$) inside the Lean kernel without invoking "
        "Bowen's pressure formalism.\n"
        "\\end{remark}",
        label="windows-rem-kernel",
    )


def patch_finstate() -> None:
    old_shared = (
        "the positive right Perron--Frobenius eigenvector $(w_v,\\lambda_C)$ on each marked "
        "strongly connected component is taken as an explicit hypothesis rather than derived "
        "via Lean matrix-eigenvalue machinery."
    )
    new_shared = (
        "moreover, \\texttt{EpiFormal/\\allowbreak PerronFrobenius.lean} ($13$ declarations "
        "audited in \\texttt{AuditPerronFrobenius.lean}, base axioms only, zero "
        "\\texttt{sorryAx}) proves the finite-dimensional Perron--Frobenius theorem "
        "from scratch via Brouwer-free Collatz--Wielandt minimax compactness and "
        "deduces the fully unconditional theorems "
        "\\texttt{thm\\_\\allowbreak finite\\_\\allowbreak state\\_\\allowbreak tail\\_\\allowbreak unconditional} "
        "on $\\R$ and "
        "\\texttt{thm\\_\\allowbreak finite\\_\\allowbreak state\\_\\allowbreak tail\\_\\allowbreak circle\\_\\allowbreak unconditional} "
        "on \\texttt{UnitAddCircle}, eliminating the external eigenvector hypothesis completely."
    )
    replace_once(SL / "sec-gauge.tex", old_shared, new_shared, label="gauge-pf")
    replace_once(SL / "sec-finstate.tex", old_shared, new_shared, label="finstate-pf")


def patch_resasymp() -> None:
    p = SL / "sec-resasymp.tex"
    old = (
        "the integer grid certificates for the narrow brackets in Table~\\ref{tab:residues-general} "
        "are run in exact Python arithmetic (\\texttt{residue\\_\\allowbreak certificate\\_\\allowbreak general\\_\\allowbreak N512.py}) "
        "and, as closed brackets, re-checked by the Lean kernel in \\texttt{Residue\\allowbreak Cert\\allowbreak Table.lean} "
        "(Remark~\\ref{rem:residue-kernel}). Moreover, all parts~(i)--(v) of "
        "Theorem~\\ref{thm:multi-residue-asymptotic} (Bowen-free proof of the Poincar\\'e-abscissa "
        "dimension formula, multi-residue phase transition at $1/2$ with two-digit witnesses "
        "$\\{2,3\\}$ and $\\{1,2\\}$, elementary Euler--Mascheroni expansion of $\\zeta(1+\\varepsilon)$, "
        "three-term subcritical asymptotics to $O((\\log m)^2/m^3)$, and supercritical "
        "$\\Theta(m^{-2s_0})$ convergence rate) are kernel-checked at Layer~A in "
        "\\texttt{EpiFormal/\\allowbreak ResidueMultiAsymptotic.lean} ($24$ public theorems "
        "audited separately in \\texttt{AuditResidueMultiAsymptotic.lean}, strictly on the three "
        "Lean base axioms \\texttt{propext}, \\texttt{Classical.choice}, and \\texttt{Quot.sound}, "
        "with zero \\texttt{sorryAx}, recorded in "
        "\\texttt{verification/\\allowbreak audit\\_\\allowbreak residue\\_\\allowbreak multi\\_\\allowbreak asymptotic\\_\\allowbreak 20261123.log})."
    )
    new = (
        "the integer grid certificates for the narrow brackets in Table~\\ref{tab:residues-general} "
        "are run in exact Python arithmetic (\\texttt{residue\\_\\allowbreak certificate\\_\\allowbreak general\\_\\allowbreak N512.py}), "
        "re-checked as closed brackets in \\texttt{Residue\\allowbreak Cert\\allowbreak Table.lean} ($27$ declarations), "
        "and upgraded to strict open inequalities completely inside the Lean kernel via monotone "
        "operator comparison in \\texttt{Residue\\allowbreak Cert\\allowbreak StrictOpen.lean} ($22$ declarations audited "
        "in \\texttt{AuditResidueCertStrictOpen.lean}; Remark~\\ref{rem:residue-kernel}). "
        "Moreover, all parts~(i)--(v) of Theorem~\\ref{thm:multi-residue-asymptotic} (Bowen-free "
        "proof of the Poincar\\'e-abscissa dimension formula, multi-residue phase transition at $1/2$ "
        "with two-digit witnesses $\\{2,3\\}$ and $\\{1,2\\}$, elementary Euler--Mascheroni expansion "
        "of $\\zeta(1+\\varepsilon)$, three-term subcritical asymptotics to $O((\\log m)^2/m^3)$, "
        "and supercritical $\\Theta(m^{-2s_0})$ convergence rate) are kernel-checked at Layer~A in "
        "\\texttt{EpiFormal/\\allowbreak ResidueMultiAsymptotic.lean} ($24$ public theorems audited "
        "separately in \\texttt{AuditResidueMultiAsymptotic.lean}, strictly on the three Lean base "
        "axioms \\texttt{propext}, \\texttt{Classical.choice}, and \\texttt{Quot.sound}, with zero "
        "\\texttt{sorryAx}, recorded in "
        "\\texttt{verification/\\allowbreak audit\\_\\allowbreak residue\\_\\allowbreak multi\\_\\allowbreak asymptotic\\_\\allowbreak 20261123.log}). "
        "Companion spin-off manuscripts~2D (\\texttt{spinoff\\_\\allowbreak critical\\_\\allowbreak and\\_\\allowbreak supercritical\\_\\allowbreak exact\\_\\allowbreak 20261125/}) "
        "and~2E (\\texttt{spinoff\\_\\allowbreak full\\_\\allowbreak convergent\\_\\allowbreak and\\_\\allowbreak even\\_\\allowbreak hurwitz\\_\\allowbreak 20261125/}) "
        "further formalize critical scaling and infinite-alphabet abscissa floors "
        "(\\texttt{GeneralAlphabetFloor.lean}, $15$ declarations; \\texttt{SupercriticalConstant.lean}, $6$ conditional "
        "declarations modulo explicit simple-pole residue \\texttt{hPole}), unconditional $\\mu(e)=2$ "
        "(\\texttt{MuEEqTwo.lean}, $9$ declarations), and the full regular convergent spectra of $e$ "
        "(\\texttt{FullConvergentSpectrum.lean}, $40$ declarations), all verified at Layer~A."
    )
    replace_once(p, old, new, label="resasymp-lean-status")


def patch_abstracts() -> None:
    old_shared = (
        "all parts~(1)--(3) of\n"
        "Theorem~\\ref{thm:finite-state-tail} (under distinct outgoing edge labels at each\n"
        "vertex and given explicit positive right Perron--Frobenius eigenvectors on marked\n"
        "strongly connected components), as well as the general-modulus ($m\\ge2$)\n"
        "uniform $24$-Lipschitz coordinate-shift sandwich, eventual-periodicity dimension\n"
        "equality, unconditional transfer-operator Hausdorff-dimension criterion\n"
        "(bypassing Bowen-pressure axioms), strict lower bound $\\dimH F_{m,r}>1/2$, upper\n"
        "bound $\\dimH F_{4,1}\\le 4/5$, step-function certificate soundness for\n"
        "Theorems~\\ref{thm:residues} and~\\ref{thm:residues-general}, and the complete\n"
        "resolvent identity, global strict separation $\\dimH F_{m,m}<\\dimH F_{m,1}=\\dimH E_m$\n"
        "for all $m\\ge2$, and two-term reciprocal-Fibonacci/metallic asymptotic expansions of\n"
        "Theorem~\\ref{thm:residues-asymptotic}, as well as the multi-residue phase\n"
        "transition, Euler--Mascheroni three-term asymptotics, and supercritical\n"
        "$\\Theta(m^{-2s_0(S)})$ rate of Theorem~\\ref{thm:multi-residue-asymptotic}\n"
        "(\\texttt{ResidueMultiAsymptotic.lean}, $24$ declarations audited in\n"
        "\\texttt{AuditResidueMultiAsymptotic.lean}) and the closed brackets of\n"
        "Table~\\ref{tab:residues-general} (\\texttt{ResidueCertTable.lean}, $27$ declarations\n"
        "audited in \\texttt{AuditResidueCert.lean})---are machine-checked in\n"
        "Lean~4 using only the base axioms \\texttt{propext}, \\texttt{Classical.choice}\n"
        "and \\texttt{Quot.sound}.\n"
        "Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector\n"
        "existence input in Theorem~\\ref{thm:finite-state-tail} and the Python-executed\n"
        "open-interval strictness verification of the narrow $m\\in\\{2,3,4,5,6\\}$ brackets\n"
        "via the pressure formalism remain outside the Lean kernel\n"
        "(Section~\\ref{sec:verification}, $937$ main audited declarations across $134$\n"
        "Lean files in \\texttt{Audit.lean} plus standalone audits across $344$ total Lean files)."
    )
    new_shared = (
        "all parts~(1)--(3) of\n"
        "Theorem~\\ref{thm:finite-state-tail} unconditionally (under distinct outgoing edge\n"
        "labels at each vertex, eliminating the Perron--Frobenius eigenvector hypothesis via\n"
        "a Brouwer-free Collatz--Wielandt minimax proof in \\texttt{PerronFrobenius.lean}, $13$\n"
        "declarations audited in \\texttt{AuditPerronFrobenius.lean}), as well as the\n"
        "general-modulus ($m\\ge2$) uniform $24$-Lipschitz coordinate-shift sandwich,\n"
        "eventual-periodicity dimension equality, unconditional transfer-operator\n"
        "Hausdorff-dimension criterion (bypassing Bowen-pressure axioms), strict lower bound\n"
        "$\\dimH F_{m,r}>1/2$, upper bound $\\dimH F_{4,1}\\le 4/5$, step-function certificate\n"
        "soundness for Theorems~\\ref{thm:residues} and~\\ref{thm:residues-general}, and the\n"
        "complete resolvent identity, global strict separation\n"
        "$\\dimH F_{m,m}<\\dimH F_{m,1}=\\dimH E_m$ for all $m\\ge2$, and two-term\n"
        "reciprocal-Fibonacci/metallic asymptotic expansions of Theorem~\\ref{thm:residues-asymptotic},\n"
        "as well as the multi-residue phase transition, Euler--Mascheroni three-term\n"
        "asymptotics, and supercritical $\\Theta(m^{-2s_0(S)})$ rate of\n"
        "Theorem~\\ref{thm:multi-residue-asymptotic} (\\texttt{ResidueMultiAsymptotic.lean}, $24$\n"
        "declarations audited in \\texttt{AuditResidueMultiAsymptotic.lean}), the closed\n"
        "brackets of Table~\\ref{tab:residues-general} (\\texttt{ResidueCertTable.lean}, $27$\n"
        "declarations audited in \\texttt{AuditResidueCert.lean}), and the strict open-interval\n"
        "inequalities of all $20$ bounds in Table~\\ref{tab:residues-general}\n"
        "(\\texttt{ResidueCertStrictOpen.lean}, $22$ declarations audited in\n"
        "\\texttt{AuditResidueCertStrictOpen.lean})---are machine-checked in Lean~4 using only\n"
        "the base axioms \\texttt{propext}, \\texttt{Classical.choice} and \\texttt{Quot.sound}\n"
        "(Section~\\ref{sec:verification}: $937$ main audited declarations across $134$ Lean\n"
        "files in \\texttt{Audit.lean} plus $156$ additional declarations across eight\n"
        "standalone audit modules spanning $356$ total Lean files, including the companion\n"
        "modules \\texttt{MuEEqTwo.lean} [$9$], \\texttt{GeneralAlphabetFloor.lean} [$15$],\n"
        "\\texttt{SupercriticalConstant.lean} [$6$ conditional declarations], and\n"
        "\\texttt{FullConvergentSpectrum.lean} [$40$] of spin-off manuscripts~2D and~2E).\n"
        "None of Theorem~\\ref{thm:finite-state-tail} or Table~\\ref{tab:residues-general}\n"
        "requires external assumptions; only the analytic simple-pole residue verification in\n"
        "Theorem~\\ref{thm:multi-residue-asymptotic}'s supercritical constant / critical\n"
        "boundary (treated in spin-off Paper~2D), the general even-period signed Hurwitz\n"
        "recurrence (spin-off Paper~2E), and the irrationality of $e+\\pi$ remain outside the\n"
        "Lean kernel."
    )
    replace_once(SL / "sec-preface.tex", old_shared, new_shared, label="sec-preface-abs")
    replace_once(SL / "frontmatter.tex", old_shared, new_shared, label="frontmatter-abs")

    replace_once(
        SL / "frontmatter-2C.tex",
        "The\n"
        "proofs---including the closed intervals of Table~\\ref{tab:residues-general} and\n"
        "the multi-residue asymptotic theory---are machine-checked in Lean~4 on the base\n"
        "axioms only, while open-interval strictness in Table~\\ref{tab:residues-general}\n"
        "combines exact Python integer certificates with the cited pressure formalism.",
        "All theorems---including finite-dimensional Perron--Frobenius eigenvector existence for\n"
        "Theorem~\\ref{thm:finite-state-tail}, the multi-residue asymptotic theory, and both the\n"
        "closed brackets and all $20$ strict open inequalities of Table~\\ref{tab:residues-general}---\n"
        "are machine-checked in Lean~4 on the base axioms only (bypassing Bowen's pressure\n"
        "formalism); exact supercritical leading constants and critical-line scaling are\n"
        "developed in companion Paper~2D.",
        label="frontmatter-2C-abs",
    )


def patch_verification() -> None:
    p = SL / "sec-verification.tex"
    old = (
        "(total\n"
        "$344$ Lean files across the repository with zero escape keywords). The build and main audit were independently reproduced on 2026-11-23 from a\n"
        "clean clone of the public repository on a separate machine (Lean~4.35.0,\n"
        "Mathlib v4.35.0): \\texttt{lake build} succeeded, the $937$\n"
        "\\texttt{\\#print axioms} outputs coincide entry by entry with the recorded log, and the $27$ residue-certificate entries depend only on the base axioms\n"
        "(\\texttt{verification/\\allowbreak colab\\_\\allowbreak rebuild\\_\\allowbreak audit\\_\\allowbreak 20261123.md}), and on 2026-11-24 a second clean-clone rebuild on a separate machine (commit \\texttt{d920a81}, which contains \\texttt{ResidueMultiAsymptotic.lean}) reproduced the $937$ main entries, the $27$ residue-certificate entries and the $24$ entries of \\texttt{AuditResidueMultiAsymptotic.lean} entry by entry, all $27+24$ on the three base axioms only (\\texttt{verification/\\allowbreak colab\\_\\allowbreak rebuild\\_\\allowbreak audit\\_\\allowbreak 20261124.md}). The portions not resolved here or lying outside\n"
        "the Lean kernel are the finite-dimensional linear-algebraic Perron--Frobenius\n"
        "eigenvector existence input on marked strongly connected components in\n"
        "Theorem~\\ref{thm:finite-state-tail} (whose positive right eigenvector is passed\n"
        "explicitly to \\texttt{thm\\_\\allowbreak finite\\_\\allowbreak state\\_\\allowbreak tail\\_\\allowbreak complete}\n"
        "and \\texttt{thm\\_\\allowbreak finite\\_\\allowbreak state\\_\\allowbreak tail\\_\\allowbreak circle\\_\\allowbreak complete}\n"
        "in \\texttt{FiniteStateComplete.lean}), the strictness of the open intervals in\n"
        "Theorem~\\ref{thm:residues} and Table~\\ref{tab:residues-general} via the\n"
        "cited pressure formalism (the closed brackets themselves are kernel-checked,\n"
        "Remark~\\ref{rem:residue-kernel}), the asymptotic rate on the critical boundary\n"
        "$s_0(S)=1/2$ and the exact supercritical leading constant in\n"
        "Theorem~\\ref{thm:multi-residue-asymptotic}, and the irrationality of $e+\\pi$,\n"
        "which remains an open problem."
    )
    new = (
        "(total $344$ Lean files on 2026-11-24, expanded on 2026-11-25 to $356$ Lean files across the repository with zero escape keywords). The build and main audit were independently reproduced on 2026-11-23 from a\n"
        "clean clone of the public repository on a separate machine (Lean~4.35.0,\n"
        "Mathlib v4.35.0): \\texttt{lake build} succeeded, the $937$\n"
        "\\texttt{\\#print axioms} outputs coincide entry by entry with the recorded log, and the $27$ residue-certificate entries depend only on the base axioms\n"
        "(\\texttt{verification/\\allowbreak colab\\_\\allowbreak rebuild\\_\\allowbreak audit\\_\\allowbreak 20261123.md}), and on 2026-11-24 a second clean-clone rebuild on a separate machine (commit \\texttt{d920a81}, which contains \\texttt{ResidueMultiAsymptotic.lean}) reproduced the $937$ main entries, the $27$ residue-certificate entries and the $24$ entries of \\texttt{AuditResidueMultiAsymptotic.lean} entry by entry, all $27+24$ on the three base axioms only (\\texttt{verification/\\allowbreak colab\\_\\allowbreak rebuild\\_\\allowbreak audit\\_\\allowbreak 20261124.md}). "
        "Subsequently, on 2026-11-25, six additional standalone Lean~4 audit modules ($105$ declarations, bringing total standalone audited declarations to $156$ and combined audited declarations to $1093$ across all $356$ Lean files, all strictly on the three Lean base axioms \\texttt{propext}, \\texttt{Classical.choice}, and \\texttt{Quot.sound} with zero \\texttt{sorryAx}) eliminated both external hypotheses from the main text and formalized companion spin-off extensions: "
        "(i)~\\texttt{AuditResidueCertStrictOpen.lean} ($22$ declarations) certifies all $20$ strict open inequalities of Table~\\ref{tab:residues-general} via monotone operator comparison directly inside Lean~4 (discharging Bowen's pressure formalism, Remark~\\ref{rem:residue-kernel}); "
        "(ii)~\\texttt{AuditPerronFrobenius.lean} ($13$ declarations) proves finite-dimensional Perron--Frobenius via Brouwer-free Collatz--Wielandt minimax compactness and delivers fully unconditional forms of Theorem~\\ref{thm:finite-state-tail}; "
        "(iii)~\\texttt{AuditMuEEqTwo.lean} ($9$ declarations) proves $\\mu(e)=2$ unconditionally at Layer~A independently of the frozen core audit; "
        "(iv)~\\texttt{AuditGeneralAlphabetFloor.lean} ($15$ declarations) and \\texttt{AuditSupercriticalConstant.lean} ($6$ conditional declarations modulo an explicit simple-pole residue input \\texttt{hPole}) support spin-off Paper~2D; and "
        "(v)~\\texttt{AuditFullConvergentSpectrum.lean} ($40$ declarations) proves the full regular convergent KL and raw spectra of $e$ for spin-off Paper~2E. "
        "The portions still lying outside the Lean kernel are the analytic simple-pole residue hypothesis \\texttt{hPole} for the exact supercritical leading constant and critical-boundary rate ($s_0(S)=1/2$) of Theorem~\\ref{thm:multi-residue-asymptotic} (proved analytically in spin-off Paper~2D), the general even-period signed Hurwitz recurrence and conditional nonlinear BLR remark (proved analytically in spin-off Paper~2E), and the irrationality of $e+\\pi$, which remains an open problem."
    )
    replace_once(p, old, new, label="sec-verification-status")


def rebuild_slice_index_and_main() -> None:
    with open(SLICE_CSV, encoding="utf-8-sig") as f:
        old_rows = {r["File"]: r["Desc"] for r in csv.DictReader(f)}
    cur_line = 1
    parts: list[bytes] = []
    out_rows: list[list[str]] = []
    for fname in ORDER:
        raw = (SL / fname).read_bytes()
        nlines = raw.decode("utf-8").count("\n")
        start = cur_line
        end = cur_line + nlines - 1
        cur_line = end + 1
        parts.append(raw)
        out_rows.append([fname, str(start), str(end), str(nlines), str(len(raw)), old_rows[fname]])

    buf = ['"File","Start","End","Lines","Bytes","Desc"']
    for row in out_rows:
        buf.append(",".join('"' + x.replace('"', '""') + '"' for x in row))
    SLICE_CSV.write_bytes(to_crlf("\n".join(buf) + "\n").encode("utf-8"))

    joined = b"".join(parts)
    MAIN_TEX.write_bytes(joined)
    print(f"Reassembled {MAIN_TEX.name}: {cur_line - 1} lines, {len(joined)} bytes.")


def main() -> None:
    patch_windows()
    patch_finstate()
    patch_resasymp()
    patch_abstracts()
    patch_verification()
    rebuild_slice_index_and_main()


if __name__ == "__main__":
    main()
