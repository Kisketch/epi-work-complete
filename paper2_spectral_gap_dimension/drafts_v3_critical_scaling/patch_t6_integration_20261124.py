r"""Paper 2 (2026-11-24): T6 integration patch producing a NEW v3 manuscript.

Purpose: produce `paper2_spectral_gap_dimension_v3_20261124.tex`, a copy of the
main manuscript with three append-only changes:

  1. The critical-scaling section `split/src_sections/sec-critical-scaling.tex`
     is \input immediately before Section "Numerical evidence" (anchor L4053).
  2. The tail equation in the proof of Theorem multi-residue-asymptotic (iv)
     (anchor L3940) has its `m^{-\varepsilon}` corrected to `m^{-1-\varepsilon}`
     (the Hurwitz tail contributes m^{-2s} zeta(2s) = m^{-1-\varepsilon}
     zeta(1+\varepsilon); the uncorrected form forces alpha ~ m and contradicts
     epsilon -> 0; the special case F_{m,m} forces alpha = 1).
  3. The six new bibliography entries of
     `split/src_sections/refs-addendum-20261124.tex` are inserted before
     \end{thebibliography} (anchor L4461).

Mode:
  * Default (no flags): DRY-RUN. Prints measured anchor line numbers, the
    verbatim anchor text, and a preview. Writes NOTHING.
  * `--apply`: writes ONLY the new v3 file. The original manuscript is never
    touched; its SHA-256 is checked before and after, and the run aborts if it
    changed. Idempotent: if the v3 file exists and already contains the
    marker, reports "already applied".

The original main manuscript is never modified (only-add discipline; the 11
base slices remain byte-concatenable).
"""
from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"
V3 = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension_v3_20261124.tex"
SECTION = ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections" / "sec-critical-scaling.tex"
ADDENDUM = ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections" / "refs-addendum-20261124.tex"

ANCHOR_SECTION = r"\section{Numerical evidence}\label{sec:num}"
ANCHOR_BIB = r"\end{thebibliography}"
OLD_TAIL = r"m^{-\varepsilon}=1+O(m^{-1}),\qquad \varepsilon:=2s-1=\frac{\alpha}{m}."
NEW_TAIL = r"m^{-1-\varepsilon}=1+O(m^{-1}),\qquad \varepsilon:=2s-1=\frac{\alpha}{m}."

MARKER = r"% [v3 integration 2026-11-24: sec-critical-scaling + tail-equation fix + refs addendum]"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def count(text: str, needle: str) -> int:
    return text.count(needle)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true", help="write the v3 file")
    args = ap.parse_args()

    if not TEX.exists():
        print(f"ERROR: missing {TEX}", file=sys.stderr)
        return 2
    for p in (SECTION, ADDENDUM):
        if not p.exists():
            print(f"ERROR: missing {p}", file=sys.stderr)
            return 2

    original_hash = sha256(TEX)
    text = TEX.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)

    # --- anchors -------------------------------------------------------------
    n_sec = count(text, ANCHOR_SECTION)
    n_bib = count(text, ANCHOR_BIB)
    n_tail = count(text, OLD_TAIL)
    print(f"[anchor] section marker occurrences: {n_sec} (expect 1)")
    print(f"[anchor] bibliography end occurrences: {n_bib} (expect 1)")
    print(f"[anchor] tail-equation occurrences: {n_tail} (expect 1)")
    if not (n_sec == n_bib == n_tail == 1):
        print("ERROR: anchor count mismatch; aborting.", file=sys.stderr)
        return 3

    sec_line = next(i + 1 for i, ln in enumerate(lines) if ANCHOR_SECTION in ln)
    bib_line = next(i + 1 for i, ln in enumerate(lines) if ANCHOR_BIB in ln)
    tail_line = next(i + 1 for i, ln in enumerate(lines) if OLD_TAIL in ln)
    print(f"[anchor] insert section before line {sec_line}")
    print(f"[anchor] insert bibitems before line {bib_line}")
    print(f"[anchor] fix tail equation at line {tail_line}")

    # --- new section input ---------------------------------------------------
    section_input = "\\input{split/src_sections/sec-critical-scaling.tex}\n"
    section_block = f"\n{MARKER}\n{section_input}"

    # --- bibliography addendum ----------------------------------------------
    add_lines = [ln for ln in ADDENDUM.read_text(encoding="utf-8").splitlines(keepends=True)
                 if not ln.lstrip().startswith("%")]
    add_block = "\n% --- v3 addendum: entries for sec-critical-scaling ---\n" + "".join(add_lines)

    if MARKER in text:
        print("[status] marker already present in the ORIGINAL; aborting (unexpected).", file=sys.stderr)
        return 4

    # --- build v3 ------------------------------------------------------------
    out: list[str] = []
    for i, ln in enumerate(lines, start=1):
        if i == tail_line:
            ln = ln.replace(OLD_TAIL, NEW_TAIL)
            assert NEW_TAIL in ln, "tail replacement failed"
        if i == sec_line:
            out.append(section_block)
        if i == bib_line:
            out.append(add_block)
        out.append(ln)

    v3_text = "".join(out)
    print(f"[preview] v3 bytes: {len(v3_text.encode('utf-8'))} (original {len(text.encode('utf-8'))})")
    print(f"[preview] v3 lines: {len(v3_text.splitlines())} (original {len(lines)})")
    print("[preview] tail fix:", NEW_TAIL[:40], "...")
    print("[preview] section block inserted before 'Numerical evidence'")
    print("[preview] addendum block inserted before \\end{thebibliography}")

    if not args.apply:
        print("\n[mode] DRY-RUN: no file written. Re-run with --apply to write the v3 file.")
        return 0

    V3.write_text(v3_text, encoding="utf-8")
    after_hash = sha256(TEX)
    if after_hash != original_hash:
        print("ERROR: original manuscript changed; aborting.", file=sys.stderr)
        return 5
    print(f"\n[apply] wrote {V3} ({len(v3_text.encode('utf-8'))} bytes)")
    print(f"[apply] original manuscript SHA-256 unchanged: {after_hash}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
