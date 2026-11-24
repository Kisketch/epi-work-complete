"""Patch paper 2 (main tex + split sources): remove stale N=256 / Python-only statements left after
patch_residues_N512_20261123.py, record the kernel-checked residue brackets in the verification
paragraph, and complete the AI-assistance disclosure. Anchors must match exactly once per file
that contains them and at least once in the main tex.
Usage: python paper2_spectral_gap_dimension/patch_stale_N512_20261123.py
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAIN = HERE / "paper2_spectral_gap_dimension.tex"
SPLIT = sorted((HERE / "split" / "src_sections").glob("*.tex"))

EDITS = [
    (r"(\texttt{verification/\allowbreak residue\_\allowbreak certificate\_\allowbreak general.py}," "\n"
     r"\texttt{\allowbreak residue\_\allowbreak certificate\_\allowbreak general\_\allowbreak N512.py},",
     r"(\texttt{verification/\allowbreak residue\_\allowbreak certificate\_\allowbreak general\_\allowbreak N512.py},"),
    (r"$256$-point dyadic numerical intervals in Theorem~\ref{thm:residues} and" "\n"
     r"Table~\ref{tab:residues-general} are certified by the reproducible exact" "\n"
     r"integer-arithmetic scripts \texttt{residue\_certificate.py} and" "\n"
     r"\texttt{residue\_\allowbreak certificate\_\allowbreak general.py}. Finally,",
     r"$512$-point dyadic numerical intervals in Theorem~\ref{thm:residues} and" "\n"
     r"Table~\ref{tab:residues-general} are certified by the reproducible exact" "\n"
     r"integer-arithmetic script \texttt{residue\_\allowbreak certificate\_\allowbreak general\_\allowbreak N512.py}," "\n"
     r"and their closed versions are kernel-checked in" "\n"
     r"\texttt{Residue\allowbreak Cert\allowbreak Table.lean} (Remark~\ref{rem:residue-kernel}). Finally,"),
    (r"systems (including ChatGPT and Codex), both for developing and drafting",
     r"systems (including ChatGPT, Codex, and Claude), both for developing and drafting"),
    (r"project-added axioms and zero \texttt{sorryAx}). The only portions not inside",
     r"project-added axioms and zero \texttt{sorryAx}); the $27$ declarations of the" "\n"
     r"residue-certificate layer (Remark~\ref{rem:residue-kernel}) are audited separately in" "\n"
     r"\texttt{AuditResidueCert.lean}, again with base axioms only. The only portions not inside"),
    (r"in \texttt{FiniteStateComplete.lean}) and the Python exact integer-arithmetic" "\n"
     r"execution of \texttt{residue\_\allowbreak certificate.py} and" "\n"
     r"\texttt{residue\_\allowbreak certificate\_\allowbreak general.py}" "\n"
     r"for the $256$-cell grid certificates in Table~\ref{tab:residues-general}" "\n"
     r"(whose transfer-operator dimension soundness theorems are verified in" "\n"
     r"\texttt{TransferOperatorDim.lean}).",
     r"in \texttt{FiniteStateComplete.lean}) and the strictness of the brackets in" "\n"
     r"Theorem~\ref{thm:residues} and Table~\ref{tab:residues-general}, which uses the" "\n"
     r"cited pressure formalism (the closed brackets themselves are kernel-checked," "\n"
     r"Remark~\ref{rem:residue-kernel})."),
    ('; only the finite-precision integer grid runs in \\texttt{residue\\_\\allowbreak certificate.py} and \\texttt{residue\\_\\allowbreak certificate\\_\\allowbreak general.py} validating the narrow brackets in Table~\\ref{tab:residues-general} execute in Python.',
     '; the integer grid certificates for the narrow brackets in Table~\\ref{tab:residues-general} are run in exact Python arithmetic (\\texttt{residue\\_\\allowbreak certificate\\_\\allowbreak general\\_\\allowbreak N512.py}) and, as closed brackets, re-checked by the Lean kernel in \\texttt{Residue\\allowbreak Cert\\allowbreak Table.lean} (Remark~\\ref{rem:residue-kernel}).'),
]


def main():
    for f in [MAIN] + SPLIT:
        t = f.read_text(encoding="utf-8")
        orig = t
        for old, new in EDITS:
            n = t.count(old)
            if f == MAIN:
                assert n == 1, (n, old[:70])
            assert n <= 1, (f.name, n, old[:70])
            t = t.replace(old, new)
        if t != orig:
            f.write_text(t, encoding="utf-8")
            print("patched", f.relative_to(HERE))


if __name__ == "__main__":
    main()
