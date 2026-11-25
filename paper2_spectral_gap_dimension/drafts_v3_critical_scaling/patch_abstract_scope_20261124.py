r"""Paper 2 (2026-11-24), task E10: abstract-scope patch (DRAFT -- do not execute).

Purpose: complete the abstract's self-report of what lies outside the Lean kernel
from the 2 items currently named (main manuscript L157-162) to the 4 items listed
in Section~\ref{sec:verification} (main manuscript L4390-4402): (1) the Perron--
Frobenius eigenvector existence input, (2) the open-interval strictness via the
pressure formalism, (3) the critical-boundary asymptotic rate and the exact
supercritical leading constant, (4) the irrationality of $e+\pi$ (open problem).

Mode:
  * Default (no flags): DRY-RUN.  Prints the measured anchor line numbers, the
    verbatim anchor text, the exact sentence that would be inserted, and an
    in-memory preview of the patched region.  Writes NOTHING.
  * `--apply`: asks the user to type `yes`; only then writes, by PURE INSERTION
    of one new sentence on its own line right after the anchor sentence's final
    `).`.  No existing character is deleted or rewritten (只增不减), and this is
    re-verified programmatically after the write (prefix/suffix/length check).
  * Idempotent: if the marker sentence is already present, both modes report
    "already applied" and do nothing.

DRAFTING STATUS (task E10 of verification/flash_task_briefs_v2_20261124.md):
this script was written by the flash drafting agent in dry-run only; `--apply`
has NEVER been run by the drafter.  Per the task brief, review and (PI-approved)
execution of this patch are reserved to the main session.
"""
import argparse
import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"

# --- anchor: rg-measured at L157 (start) and L162 (end of sentence, including
# --- the parenthetical audit-count note); the brief cites L157-160 for the core.
ANCHOR_START = "Only the finite-dimensional linear-algebraic Perron--Frobenius eigenvector"
ANCHOR_END = "total Lean files)."

# --- idempotency marker: distinctive substring of the inserted sentence ---
MARKER = "four-item list recorded in Section~\\ref{sec:verification}"

# --- the new sentence, in English, mirroring the four-item scope statement of
# --- Section verification (main manuscript L4390-4402); the two mid-item
# --- parentheticals of the source are omitted for abstract brevity, all four
# --- item phrasings are otherwise verbatim from L4391-4402.
NEW_SENTENCE = (
    r"Beyond the two items just named, the complete set of portions not resolved here or lying "
    r"outside the Lean kernel is exactly the four-item list recorded in "
    r"Section~\ref{sec:verification}: the finite-dimensional linear-algebraic "
    r"Perron--Frobenius eigenvector existence input in Theorem~\ref{thm:finite-state-tail}, the "
    r"strictness of the open intervals in Theorem~\ref{thm:residues} and "
    r"Table~\ref{tab:residues-general} via the cited pressure formalism, the asymptotic rate on "
    r"the critical boundary $s_0(S)=1/2$ and the exact supercritical leading constant in "
    r"Theorem~\ref{thm:multi-residue-asymptotic}, and the irrationality of $e+\pi$, which "
    r"remains an open problem."
)


def line_of(text, idx):
    """1-based line number of character index idx."""
    return text.count("\n", 0, idx) + 1


def locate(text):
    """Return (start_idx, end_idx, insert_pos, nl) with uniqueness asserted."""
    n = text.count(ANCHOR_START)
    assert n == 1, "anchor start marker found %d times (expected 1)" % n
    start = text.find(ANCHOR_START)
    n2 = text.count(ANCHOR_END)
    assert n2 == 1, "anchor end marker found %d times (expected 1)" % n2
    end = text.find(ANCHOR_END)
    assert end > start, "anchor end marker precedes start marker"
    pos = end + len(ANCHOR_END)
    nl = "\r\n" if "\r\n" in text else "\n"
    return start, end, pos, nl


def region(text, lo, hi):
    """Verbatim lines lo..hi (1-based, inclusive) of text."""
    lines = text.split("\n")
    return [lines[i - 1].rstrip("\r") for i in range(lo, hi + 1)]


def main():
    ap = argparse.ArgumentParser(
        description="E10 abstract-scope patch (default dry-run; --apply + typed 'yes' to write)")
    ap.add_argument("--apply", action="store_true",
                    help="write the patch (still requires typing 'yes' at the prompt)")
    args = ap.parse_args()

    raw = TEX.read_bytes()
    text = raw.decode("utf-8")
    sha_old = hashlib.sha256(raw).hexdigest()
    print("== patch_abstract_scope_20261124 (task E10) ==")
    print("mode          :", "APPLY" if args.apply else "DRY-RUN (no files will be written)")
    print("target        :", str(TEX))
    print("target bytes  :", len(raw))
    print("target sha256 :", sha_old)
    print("newline style :", "CRLF" if "\r\n" in text else "LF")

    if MARKER in text:
        print("status        : ALREADY APPLIED (marker sentence present) -- nothing to do.")
        return

    start, end, pos, nl = locate(text)
    start_line, end_line = line_of(text, start), line_of(text, end + len(ANCHOR_END))
    insert = nl + NEW_SENTENCE
    print("anchor start  : line %d  (marker: Only the finite-dimensional ... eigenvector)" % start_line)
    print("anchor end    : line %d  (end marker: %s)" % (end_line, ANCHOR_END))
    print("insertion pos : char offset %d (right after the anchor's final ')';" % pos)
    print("                the new sentence becomes line %d; no existing character moves." % (end_line + 1))
    print()
    print("--- anchor original text (verbatim, lines %d-%d) ---" % (start_line, end_line))
    for ln in region(text, start_line, end_line):
        print(ln)
    print()
    print("--- sentence to be inserted (pure insertion of one new line) ---")
    print(NEW_SENTENCE)
    print()

    patched = text[:pos] + insert + text[pos:]
    print("--- preview of the patched region (in memory only; new line numbers) ---")
    for i, ln in enumerate(region(patched, start_line - 1, end_line + 4), start=start_line - 1):
        print("%5d: %s" % (i, ln))
    print()

    if not args.apply:
        print("== DRY-RUN complete: nothing written. ==")
        return

    answer = input("Type 'yes' to write the patch to %s: " % TEX.name)
    if answer.strip() != "yes":
        print("ABORTED: confirmation was not exactly 'yes'; nothing written.")
        return

    # Re-read and re-locate immediately before writing (guard against races).
    raw2 = TEX.read_bytes()
    text2 = raw2.decode("utf-8")
    assert text2 == text, "target changed on disk since dry-run; re-run"
    start2, end2, pos2, nl2 = locate(text2)
    assert (start2, end2, pos2) == (start, end, pos), "anchor moved; re-run"
    insert2 = nl2 + NEW_SENTENCE
    patched2 = text2[:pos2] + insert2 + text2[pos2:]

    # Pure-insertion verification: prefix and suffix byte-identical, length grows
    # by exactly len(insert2), i.e. no existing character deleted or rewritten.
    assert patched2[:pos2] == text2[:pos2], "pure insertion violated (prefix)"
    assert patched2[pos2 + len(insert2):] == text2[pos2:], "pure insertion violated (suffix)"
    assert len(patched2) == len(text2) + len(insert2), "pure insertion violated (length)"
    out = patched2.encode("utf-8")
    TEX.write_bytes(out)
    sha_new = hashlib.sha256(TEX.read_bytes()).hexdigest()
    print("written       : %s" % str(TEX))
    print("inserted chars: %d (one new line: line %d)" % (len(insert2), end_line + 1))
    print("sha256 before :", sha_old)
    print("sha256 after  :", sha_new)
    print("pure insertion: verified (prefix/suffix/length checks passed).")


if __name__ == "__main__":
    try:
        main()
    except AssertionError as exc:
        print("REFUSED: %s" % exc)
        sys.exit(2)
