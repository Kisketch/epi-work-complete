"""Record the independent clean rebuild + audit (Google Colab, 2026-11-23) in both papers.

Source of the facts: verification/colab_rebuild_audit_20261123.md (lake build exit 0;
937 #print axioms outputs identical entry by entry to audit_final_20261122.log;
AuditResidueCert.lean 27 entries, base axioms only).  Paper 1 AI disclosure also lists Claude.
Paper 2 edits are applied to the main tex and to every split slice that contains the anchor.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P1 = ROOT / "paper1_e_plus_pi" / "01_main_paper" / "paper1_e_plus_pi.tex"
P2 = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"
P2_SPLIT = sorted((ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections").glob("*.tex"))

REBUILD = (r" The build and this audit were independently reproduced on 2026-11-23 from a" "\n"
           r"clean clone of the public repository on a separate machine (Lean~4.35.0," "\n"
           r"Mathlib v4.35.0): \texttt{lake build} succeeded, and the $937$" "\n"
           r"\texttt{\#print axioms} outputs coincide entry by entry with the recorded log" "\n"
           r"(\texttt{verification/\allowbreak colab\_\allowbreak rebuild\_\allowbreak audit\_\allowbreak 20261123.md}).")

P1_EDITS = [
    (r"generative AI systems (including ChatGPT and Codex), both for",
     r"generative AI systems (including ChatGPT, Codex, and Claude), both for"),
    ("\n" r"\texttt{sorryAx}). The remaining" "\n",
     "\n" r"\texttt{sorryAx})." + REBUILD + r" The remaining" "\n"),
]

P2_EDITS = [
    (r"\texttt{AuditResidueCert.lean}, again with base axioms only. The only portions not inside",
     r"\texttt{AuditResidueCert.lean}, again with base axioms only." + REBUILD.replace(
         "and the $937$", "the $937$").replace(
         "coincide entry by entry with the recorded log",
         "coincide entry by entry with the recorded log, and the $27$ residue-certificate entries depend only on the base axioms")
     + r" The only portions not inside"),
]


def apply(files, edits, required):
    texts = {f: f.read_text(encoding="utf-8") for f in files}
    for old, new in edits:
        hits = 0
        for f in files:
            n = texts[f].count(old)
            assert n <= 1, (f.name, n, old[:60])
            if n:
                texts[f] = texts[f].replace(old, new)
                hits += 1
        assert hits >= 1 and (required is None or old in files[0].read_text(encoding="utf-8")), old[:70]
    for f in files:
        if texts[f] != f.read_text(encoding="utf-8"):
            f.write_text(texts[f], encoding="utf-8")
            print("patched", f.relative_to(ROOT))


if __name__ == "__main__":
    apply([P1], P1_EDITS, True)
    apply([P2] + P2_SPLIT, P2_EDITS, True)
