"""Entry-by-entry comparison of a fresh `#print axioms` output against a committed reference log.

Usage:
    python verification/compare_audit_logs.py OUTPUT REFERENCE [--count N] [--only-axioms a,b,c]
    python verification/compare_audit_logs.py OUTPUT --count N --only-axioms a,b,c   # no reference

Each entry is one `'decl' depends on axioms: [...]` or `'decl' does not depend on any axioms`
message; Lean wraps long axiom lists over several lines, so continuation lines are joined and
whitespace is normalised before comparing.  Lines starting with `#` in a reference log are
treated as provenance comments.  Any other line in OUTPUT (errors, warnings, stray text) is a
failure, as is any difference in the ordered list of entries.  Exit code 0 only if everything
matches.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ENTRY_RE = re.compile(r"^'(?P<name>.+)'\s+(?:depends on axioms:\s*\[(?P<axs>.*)\]|does not depend on any axioms)\s*$")
ENTRY_START_RE = re.compile(r"^'.+'\s+(?:depends on axioms:|does not depend on any axioms)")


def read_text_auto(path: Path) -> str:
    """Read UTF-8, UTF-8-SIG, or UTF-16 logs (PowerShell redirection writes UTF-16)."""
    raw = path.read_bytes()
    if raw.startswith((b"\xff\xfe", b"\xfe\xff")):
        text = raw.decode("utf-16")
    elif raw.startswith(b"\xef\xbb\xbf"):
        text = raw.decode("utf-8-sig")
    elif b"\x00" in raw[:400]:
        text = raw.decode("utf-16-le", errors="replace")
    else:
        text = raw.decode("utf-8", errors="replace")
    return text.lstrip("﻿")


def parse(path: Path, allow_comments: bool) -> tuple[list[tuple[str, tuple[str, ...]]], list[str]]:
    """Return (entries, stray_lines).  Each entry is (name, axioms-in-printed-order)."""
    blocks: list[str] = []
    stray: list[str] = []
    for line in read_text_auto(path).splitlines():
        if not line.strip():
            continue
        if ENTRY_START_RE.match(line):
            blocks.append(line.strip())
        elif line[:1].isspace() and blocks and "]" not in blocks[-1]:
            blocks[-1] += " " + line.strip()
        elif allow_comments and line.startswith("#"):
            continue
        else:
            stray.append(line)
    entries = []
    for block in blocks:
        m = ENTRY_RE.match(" ".join(block.split()))
        if not m:
            stray.append(block)
            continue
        axs = tuple(a.strip() for a in (m.group("axs") or "").split(",") if a.strip())
        entries.append((m.group("name"), axs))
    return entries, stray


def fmt(entry: tuple[str, tuple[str, ...]]) -> str:
    name, axs = entry
    return f"'{name}' -> [{', '.join(axs)}]" if axs else f"'{name}' -> (no axioms)"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("output", type=Path, help="fresh output of `lake env lean <Audit file>`")
    ap.add_argument("reference", type=Path, nargs="?", help="committed reference log")
    ap.add_argument("--count", type=int, help="expected number of entries")
    ap.add_argument("--only-axioms", help="comma-separated set every entry's axioms must lie within")
    args = ap.parse_args()

    errors: list[str] = []
    out_entries, out_stray = parse(args.output, allow_comments=False)
    print(f"Output    {args.output}: {len(out_entries)} entries")
    for line in out_stray:
        errors.append(f"unexpected line in output: {line}")

    names = [n for n, _ in out_entries]
    dups = sorted({n for n in names if names.count(n) > 1})
    if dups:
        errors.append(f"duplicate entries in output: {dups}")

    if args.reference is not None:
        ref_entries, ref_stray = parse(args.reference, allow_comments=True)
        print(f"Reference {args.reference}: {len(ref_entries)} entries")
        for line in ref_stray:
            errors.append(f"unparseable line in reference: {line}")
        if out_entries != ref_entries:
            out_map, ref_map = dict(out_entries), dict(ref_entries)
            for n in sorted(ref_map.keys() - out_map.keys()):
                errors.append(f"missing from output: {fmt((n, ref_map[n]))}")
            for n in sorted(out_map.keys() - ref_map.keys()):
                errors.append(f"not in reference: {fmt((n, out_map[n]))}")
            for n in sorted(out_map.keys() & ref_map.keys()):
                if out_map[n] != ref_map[n]:
                    errors.append(f"axioms differ for '{n}': output {list(out_map[n])} vs reference {list(ref_map[n])}")
            if out_map == ref_map:
                errors.append("same entries but in a different order")
        diff_count = sum(1 for a, b in zip(out_entries, ref_entries) if a != b) + abs(len(out_entries) - len(ref_entries))
        print(f"Positional entry differences: {diff_count}")

    if args.count is not None and len(out_entries) != args.count:
        errors.append(f"expected {args.count} entries, got {len(out_entries)}")

    if args.only_axioms is not None:
        allowed = {a.strip() for a in args.only_axioms.split(",") if a.strip()}
        bad = [fmt(e) for e in out_entries if not set(e[1]) <= allowed]
        for b in bad:
            errors.append(f"axioms outside {sorted(allowed)}: {b}")
        distinct = sorted({frozenset(e[1]) for e in out_entries}, key=sorted)
        print(f"Distinct axiom sets: {[sorted(s) for s in distinct]}")

    if errors:
        print(f"FAILED ({len(errors)} problem(s)):")
        for e in errors:
            print("  " + e)
        return 1
    print("AUDIT OUTPUT MATCHES.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
