r"""Paper 1 consistency patch (2026-11-23), from a read-only consistency audit.

- Two places quoted a stale audit snapshot (872 declarations / 131 files / 849 base-only)
  while citing audit_final_20261122.log, which has 937 entries; the paper's appendix and
  README say 937 / 134 / 914 + 23.  Unified to 937 / 134 / 914.
- Honesty statement: list every preprint the paper conditions on (Bertolin, Fischler--Rivoal,
  the OpenAI claim); Bai is used only for a numerical comparison.
- Meiburg: only the Flint Hills case is formalized; the general statement is preprint-only.
  The "no longer rests on that preprint" claim holds for the formal route only.
- Stale "delta axioms" wording (deltaSel_tendsto_zero is a theorem); Ap'ery typo; missing
  \cite{Yu2026} for arXiv:2606.17303.
Each anchor must occur exactly `count` times.
"""
from pathlib import Path

F = Path(__file__).resolve().parent / "paper1_e_plus_pi.tex"

EDITS = [
    (r"(872 audited declarations project-wide across 131 Lean files,",
     r"(937 audited declarations project-wide across 134 Lean files,", 1),
    (r"(872 audited" "\n" r"declarations project-wide across 131 Lean files as of 2026-11-22, recorded in",
     r"(937 audited" "\n" r"declarations project-wide across 134 Lean files as of 2026-11-22, recorded in", 1),
    ("\n" r"849 depend only on the Lean base axioms \texttt{propext},",
     "\n" r"914 depend only on the Lean base axioms \texttt{propext},", 1),
    (r"Results that depend on unreviewed preprints (Bertolin \cite{Bertolin2026}, Bai \cite{Bai2026}) are stated conditionally and flagged as such.",
     r"Results that depend on unreviewed preprints (Bertolin \cite{Bertolin2026}, Fischler--Rivoal \cite{FischlerRivoal2026}, and the external claim \cite{OpenAI2026}) are stated conditionally and flagged as such; Bai's preprint \cite{Bai2026} is used only for a numerical comparison.", 1),
    (r"its Flint Hills case is now machine-verified (Appendix~\ref{sec:lean}), so the bridge no longer rests on that preprint.",
     r"its Flint Hills case is now formalized in Lean (Appendix~\ref{sec:lean}), so the formal version of the bridge no longer rests on that preprint, while the paper's general statement of Meiburg's criterion remains preprint-dependent.", 1),
    (r"\begin{theorem}[Meiburg, preprint; Flint Hills case machine-verified]\label{thm:meiburg}",
     r"\begin{theorem}[Meiburg, preprint; only the Flint Hills case is formalized in Lean]\label{thm:meiburg}", 1),
    (r"$\delta$ axioms", r"$\delta$ error theorems", 3),
    (r"Ap'ery", r"Ap\'ery", 1),
    (r"(arXiv:2606.17303)", r"(arXiv:2606.17303, \cite{Yu2026})", 1),
]


def main():
    t = F.read_text(encoding="utf-8")
    for old, new, count in EDITS:
        assert t.count(old) == count, (t.count(old), count, old[:70])
        t = t.replace(old, new)
    F.write_text(t, encoding="utf-8")
    print("patched", F.name)


if __name__ == "__main__":
    main()
