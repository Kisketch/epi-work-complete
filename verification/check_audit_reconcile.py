"""Airtight reconciliation between Audit.lean and an audit log file."""
import re
import sys
from pathlib import Path

def read_text_auto(path: Path) -> str:
    """Read UTF-8, UTF-8-SIG, or UTF-16 (Windows PowerShell redirection) logs cleanly."""
    raw = path.read_bytes()
    if raw.startswith((b"\xff\xfe", b"\xfe\xff")):
        text = raw.decode("utf-16")
    elif raw.startswith(b"\xef\xbb\xbf"):
        text = raw.decode("utf-8-sig")
    elif b"\x00" in raw[:400]:
        text = raw.decode("utf-16-le", errors="replace")
    else:
        text = raw.decode("utf-8", errors="replace")
    return text.lstrip("\ufeff")


root = Path(__file__).resolve().parent.parent
log_path = Path(sys.argv[1]) if len(sys.argv) > 1 else root / "verification" / "audit_final_20261122.log"

audit_src = read_text_auto(root / "epi_formal" / "Audit.lean")
audit_log = read_text_auto(log_path)

prints = re.findall(r"^#print axioms\s+(\S+)", audit_src, re.M)
full_entries = re.findall(r"^'(.+?)'\s+depends on axioms:\s*\[([^\]]*)\]", audit_log, re.M)
no_axioms = re.findall(r"^'(.+?)'\s+does not depend on any axioms", audit_log, re.M)

print(f"Log file: {log_path}")
print(f"Audit.lean #print axioms count: {len(prints)} (unique: {len(set(prints))})")
print(
    f"Log depends-on-axioms count: {len(full_entries)}, "
    f"no-axioms count: {len(no_axioms)}, total: {len(full_entries) + len(no_axioms)}"
)

log_map = {}
for name, axs in full_entries:
    log_map[name] = [a.strip() for a in axs.split(",") if a.strip()]
for name in no_axioms:
    log_map[name] = []

print(f"Unique declarations in log: {len(log_map)}")
missing_in_log = set(prints) - set(log_map.keys())
extra_in_log = set(log_map.keys()) - set(prints)
print(f"In Audit.lean but not log ({len(missing_in_log)}): {sorted(missing_in_log)}")
print(f"In log but not Audit.lean ({len(extra_in_log)}): {sorted(extra_in_log)}")

sorry_decls = [k for k, v in log_map.items() if "sorryAx" in v]
print(f"sorryAx declarations: {len(sorry_decls)} -> {sorry_decls}")

core = {"propext", "Classical.choice", "Quot.sound"}
non_core = {k: [a for a in v if a not in core] for k, v in log_map.items() if any(a not in core for a in v)}
print(f"Declarations using non-core axioms: {len(non_core)}")
all_extra = sorted({a for v in non_core.values() for a in v})
print(f"Distinct non-core axioms: {all_extra}")

whitelist = {"e_transcendental", "pi_transcendental", "mu_e_eq_two"}
unexpected_axioms = set(all_extra) - whitelist
print(f"Unexpected (project-added) axioms: {sorted(unexpected_axioms)}")

# Escape-keyword scan across all .lean files in epi_formal/ (excluding .lake/)
lean_files = sorted(
    p for p in (root / "epi_formal").rglob("*.lean")
    if ".lake" not in p.relative_to(root / "epi_formal").parts
)
escape_hits = []
axiom_decls = []
for lf in lean_files:
    txt = lf.read_text(encoding="utf-8", errors="replace")
    # Strip block comments /- ... -/ and line comments -- ...
    no_block = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    for lineno, line in enumerate(no_block.splitlines(), 1):
        code = re.sub(r"--.*$", "", line)
        if re.search(r"\b(sorry|admit|native_decide|implemented_by|extern|unsafe|partial|opaque)\b", code):
            escape_hits.append((str(lf.relative_to(root)), lineno, code.strip()))
        if re.search(r"\baxiom\s+", code):
            axiom_decls.append((str(lf.relative_to(root)), lineno, code.strip()))

print(f"Scanned {len(lean_files)} Lean files; escape keyword hits: {len(escape_hits)}")
if escape_hits:
    for h in escape_hits[:20]:
        print("  ESCAPE:", h)
print(f"Source axiom declarations ({len(axiom_decls)}):")
for a in axiom_decls:
    print("  AXIOM:", a)

new_prefixes = (
    "WindowTreePrune.",
    "WindowAsympThresh.",
    "WindowFrostmanDischarge.",
    "WindowPaperScale.",
    "WindowCFRealize.",
    "WindowCFBridge.",
    "WindowNoShortCFRealize.",
    "WindowPrescribedCFRealize.",
    "WindowBoundedUpper.",
    "GoldenHeadCutoff.",
    "AffineWindowAudit.",
    "DigitTailBound.",
    "DensityCube.",
    "OrbitAndFlow.",
    "ResearchAdvance.",
    "TraceMarkov.",
    "WindowShortAeRealize.",
    "ResidueModGeneral.",
    "TransferOperatorDim.",
    "FiniteStateComplete.",
)
new_exact = {"rational_endpoint_cutoff"}
new_decls = {k: v for k, v in log_map.items() if k.startswith(new_prefixes) or k in new_exact}
new_non_core = {k: v for k, v in new_decls.items() if any(a not in core for a in v)}
print(f"2026-11-22 new/integrated declarations audited: {len(new_decls)}, non-core: {len(new_non_core)}")
print(f"Core-only declarations: {len(log_map) - len(non_core)}, whitelisted-classical declarations: {len(non_core)}")

# Strict assertions
assert len(prints) == len(set(prints)), "Duplicate #print axioms in Audit.lean!"
assert len(prints) == len(log_map), f"Count mismatch: {len(prints)} vs {len(log_map)}"
assert not missing_in_log and not extra_in_log, "Bijection mismatch!"
assert len(sorry_decls) == 0, f"Found sorryAx in {sorry_decls}"
assert len(unexpected_axioms) == 0, f"Found unexpected axioms: {unexpected_axioms}"
assert len(non_core) == 23, f"Expected strictly 23 whitelisted classical declarations, got {len(non_core)}"
assert len(escape_hits) == 0, f"Found escape keywords: {escape_hits}"
assert len(axiom_decls) == 3, f"Expected strictly 3 source axiom declarations, got {len(axiom_decls)}: {axiom_decls}"
assert len(new_decls) == 226, f"Expected 226 new/integrated declarations (182 + 44), got {len(new_decls)}"
assert len(new_non_core) == 0, f"New declarations used non-core axioms: {new_non_core}"
print("ALL RECONCILIATION CHECKS PASSED!")
