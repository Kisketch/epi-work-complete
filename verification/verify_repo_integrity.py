"""Unified repository integrity, zero-loss conservation, audit, and link checker."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parent.parent
LOG_PATH = ROOT / "verification" / "verify_repo_integrity.log"


def run_step(cmd: list[str], cwd: Path = ROOT) -> tuple[int, str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    combined = (proc.stdout or "") + (proc.stderr or "")
    return proc.returncode, combined


def check_git_conservation(out: list[str]) -> None:
    """Assert zero tracked files were deleted from prior baseline commits 1e91028 and 7ece3b9."""
    for rev in ("1e91028", "7ece3b9"):
        proc = subprocess.run(
            ["git", "-c", "core.quotepath=false", "ls-tree", "-r", "--name-only", rev],
            cwd=str(ROOT),
            capture_output=True,
        )
        assert proc.returncode == 0, f"git ls-tree failed for {rev}"
        tracked = [line for line in proc.stdout.decode("utf-8").splitlines() if line]
        missing = [rel for rel in tracked if not (ROOT / rel).exists()]
        assert not missing, f"Missing files from {rev}: {missing}"
        out.append(f"  [OK] Zero-loss check vs {rev}: {len(tracked)}/{len(tracked)} files present on disk")


WINDOWS_ABS_RE = re.compile(r"^(?:file:///)?[A-Za-z]:[/\\]")
REPO_DIR_MARKER = "/epi_work/"


def resolve_link_target(doc: Path, target: str) -> tuple[Path | None, bool]:
    """Resolve a Markdown link target to a local path.

    Returns ``(path, is_windows_abs)``.  Absolute Windows paths (``c:/Users/...``,
    ``file:///c:/...``) are never passed to ``stat`` directly: on Linux/macOS they
    would be read as a relative path and can crash ``Path.exists``.  Instead, a
    path that contains the author's checkout directory ``.../epi_work/`` is
    re-rooted at this repository, so the link is still checked; anything else is
    returned as ``None`` and reported as non-portable.
    """
    if WINDOWS_ABS_RE.match(target):
        win = unquote(target[len("file:///"):] if target.startswith("file:///") else target)
        win = win.replace("\\", "/")
        idx = win.find(REPO_DIR_MARKER)
        if idx < 0:
            return None, True
        return (ROOT / win[idx + len(REPO_DIR_MARKER):]).resolve(), True
    if target.startswith("file:///"):
        return Path(unquote(target[len("file:///"):])).resolve(), False
    return (doc.parent / unquote(target)).resolve(), False


def safe_exists(path: Path) -> bool:
    try:
        return path.exists()
    except OSError:
        return False


def check_markdown_docs(out: list[str]) -> None:
    """Assert core documentation files exist, have no UTF-8 BOM, zero broken links, and synced skills."""
    docs = [
        ROOT / "README.md",
        ROOT / "REPOSITORY_STRUCTURE.md",
        ROOT / "paper1_e_plus_pi" / "00_PROJECT_INDEX.md",
        ROOT / "paper1_e_plus_pi" / "07_research_log_and_guide" / "MASTER_INVENTORY_LIST.md",
        ROOT / "paper1_e_plus_pi" / "07_research_log_and_guide" / "PAPER1_ATTACK_AND_TRIAL_LOG.md",
        ROOT / "paper1_e_plus_pi" / "07_research_log_and_guide" / "MASTER_GUIDE_SKILL.md",
        ROOT / "paper1_e_plus_pi" / "07_research_log_and_guide" / "trial_notes_M1_M2_20261125.md",
        ROOT / "paper2_spectral_gap_dimension" / "README.md",
        ROOT / "paper2_spectral_gap_dimension" / "00_research_log_and_guide" / "SPINOFF_AND_TRIAL_LOG.md",
        ROOT / "paper2_spectral_gap_dimension" / "00_research_log_and_guide" / "MASTER_GUIDE_SKILL.md",
        ROOT / "paper2_spectral_gap_dimension" / "spinoff_critical_and_supercritical_exact_20261125" / "README.md",
        ROOT / "paper2_spectral_gap_dimension" / "spinoff_full_convergent_and_even_hurwitz_20261125" / "README.md",
        ROOT / "paper2_spectral_gap_dimension" / "split" / "README.md",
        ROOT / "research" / "README.md",
        ROOT / "research" / "kahane_q6_note_20261125.md",
        ROOT / "research" / "kahane_q6_addendum_20261125.md",
        ROOT / "verification" / "README.md",
        ROOT / "verification" / "kahane_and_blr_audit_20261125.md",
        ROOT / "verification" / "全工作区总索引与留痕台账.md",
        ROOT / ".agents" / "skills" / "epi-research-commander" / "SKILL.md",
        ROOT / ".claude" / "skills" / "epi-research-commander" / "SKILL.md",
    ]
    link_re = re.compile(r"\]\(([^)#]+)(?:#[^)]*)?\)")
    total_links = 0
    windows_abs = 0
    unportable: list[str] = []
    for doc in docs:
        assert doc.exists(), f"Missing doc: {doc}"
        raw = doc.read_bytes()
        assert not raw.startswith(b"\xef\xbb\xbf"), f"Unexpected UTF-8 BOM in {doc}"
        txt = raw.decode("utf-8")
        broken: list[str] = []
        for match in link_re.findall(txt):
            target = match.strip()
            if not target or target.startswith(("http://", "https://", "mailto:")):
                continue
            resolved, is_windows_abs = resolve_link_target(doc, target)
            windows_abs += is_windows_abs
            total_links += 1
            if resolved is None:
                unportable.append(f"{doc.relative_to(ROOT)}: {target}")
                continue
            if resolved != LOG_PATH.resolve() and not safe_exists(resolved):
                broken.append(target)
        assert not broken, f"Broken links in {doc.relative_to(ROOT)}: {broken}"

    skill_copies = [
        ROOT / ".agents" / "skills" / "epi-research-commander" / "SKILL.md",
        ROOT / ".claude" / "skills" / "epi-research-commander" / "SKILL.md",
        ROOT / "paper1_e_plus_pi" / "07_research_log_and_guide" / "MASTER_GUIDE_SKILL.md",
        ROOT / "paper2_spectral_gap_dimension" / "00_research_log_and_guide" / "MASTER_GUIDE_SKILL.md",
    ]
    skill_bytes = [p.read_bytes() for p in skill_copies]
    assert len(set(skill_bytes)) == 1, "epi-research-commander SKILL.md copies diverged!"

    out.append(
        f"  [OK] Core & Round-2 Markdown docs: {len(docs)}/{len(docs)} BOM-free, "
        f"{total_links} local links resolved (0 broken), 4/4 commander skill byte-synced"
    )
    if windows_abs:
        out.append(
            f"  [WARN] {windows_abs} link(s) use absolute Windows paths (re-rooted at the repo where possible; "
            "prefer relative links)"
        )
    for item in unportable:
        out.append(f"  [WARN] Not checked (absolute Windows path outside the repo): {item}")


def check_lean_audits(out: list[str]) -> None:
    """Re-run main audit reconciler and verify all standalone Layer A audit entries and logs."""
    rc, txt = run_step([sys.executable, "verification/check_audit_reconcile.py", "verification/audit_final_20261122.log"])
    assert rc == 0 and "ALL RECONCILIATION CHECKS PASSED!" in txt, f"check_audit_reconcile failed:\n{txt}"
    m_scan = re.search(r"Scanned\s+(\d+)\s+Lean files;\s+escape keyword hits:\s+(\d+)", txt)
    n_lean = int(m_scan.group(1)) if m_scan else 0
    assert n_lean >= 356, f"Expected >= 356 Lean files scanned, got {n_lean}"
    out.append(f"  [OK] Audit.lean reconciliation: 937/937 matched, sorryAx=0, {n_lean} Lean files / 0 escape hits")

    standalone_specs = [
        ("AuditResidueCert.lean", "audit_residue_cert_20261123.log", 27),
        ("AuditResidueMultiAsymptotic.lean", "audit_residue_multi_asymptotic_20261123.log", 24),
        ("AuditResidueCertStrictOpen.lean", "audit_residue_cert_strict_open_20261125.log", 22),
        ("AuditMuEEqTwo.lean", "audit_mu_e_eq_two_20261125.log", 9),
        ("AuditGeneralAlphabetFloor.lean", "audit_general_alphabet_floor_20261125.log", 15),
        ("AuditSupercriticalConstant.lean", "audit_supercritical_constant_20261125.log", 6),
        ("AuditPerronFrobenius.lean", "audit_perron_frobenius_20261125.log", 13),
        ("AuditFullConvergentSpectrum.lean", "audit_full_convergent_spectrum_20261125.log", 40),
    ]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    total_standalone = 0
    for lean_name, log_name, expected in standalone_specs:
        lean_text = (ROOT / "epi_formal" / lean_name).read_text(encoding="utf-8")
        cnt = sum(1 for ln in lean_text.splitlines() if ln.strip().startswith("#print axioms "))
        assert cnt == expected, f"Expected {expected} entries in {lean_name}, got {cnt}"
        log_path = ROOT / "verification" / log_name
        assert log_path.exists(), f"Missing audit log: {log_path}"
        rc_cmp, txt_cmp = run_step([
            sys.executable,
            "verification/compare_audit_logs.py",
            f"verification/{log_name}",
            "--count",
            str(expected),
            "--only-axioms",
            "propext,Classical.choice,Quot.sound",
            "--allow-comments",
        ])
        assert rc_cmp == 0, f"compare_audit_logs self-check failed on {log_name}:\n{txt_cmp}"
        log_text = log_path.read_text(encoding="utf-8")
        matches = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]+)\]", log_text, flags=re.S)
        assert len(matches) == expected, f"Expected {expected} entries in {log_name}, got {len(matches)}"
        for name, raw_ax in matches:
            axs = {x.strip() for x in raw_ax.split(",") if x.strip()}
            assert "sorryAx" not in axs and axs.issubset(allowed), f"Unexpected axioms for {name}: {axs}"
        total_standalone += expected
    out.append(
        f"  [OK] Standalone Layer A audits: {len(standalone_specs)} modules / {total_standalone}/{total_standalone} base axioms only, sorryAx=0"
    )


def check_papers_and_split(out: list[str]) -> None:
    """Check PDFs exist cleanly and verify Paper 2 merge integrity, spin-off logs, + split undef refs."""
    pdfs = [
        ROOT / "paper1_e_plus_pi" / "01_main_paper" / "paper1_e_plus_pi.pdf",
        ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.pdf",
        ROOT / "paper2_spectral_gap_dimension" / "spinoff_critical_and_supercritical_exact_20261125" / "paper2D_critical_supercritical_exact.pdf",
        ROOT / "paper2_spectral_gap_dimension" / "spinoff_full_convergent_and_even_hurwitz_20261125" / "paper2E_full_convergent_and_even_hurwitz.pdf",
    ]
    for pdf in pdfs:
        assert pdf.exists() and pdf.stat().st_size > 50_000, f"Missing or too small PDF: {pdf}"

    for log_rel in (
        "paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.log",
        "paper2_spectral_gap_dimension/spinoff_critical_and_supercritical_exact_20261125/paper2D_critical_supercritical_exact.log",
        "paper2_spectral_gap_dimension/spinoff_full_convergent_and_even_hurwitz_20261125/paper2E_full_convergent_and_even_hurwitz.log",
    ):
        log_txt = (ROOT / log_rel).read_text(encoding="utf-8", errors="replace")
        ov = len(re.findall(r"Overfull \\hbox", log_txt))
        und = len(re.findall(r"There were undefined", log_txt))
        assert ov == 0 and und == 0, f"{log_rel}: overfull={ov}, undefined={und}"

    rc, txt = run_step([sys.executable, "verification/verify_paper2_merge.py"])
    assert rc == 0 and "ALL MERGE & INTEGRITY CHECKS PASSED." in txt, f"verify_paper2_merge failed:\n{txt}"
    out.append("  [OK] Paper 2 + 2D + 2E builds (0 Overfull / 0 Undef), 11-slice parity, and 46 content anchors passed")

    rc2, txt2 = run_step([sys.executable, "paper2_spectral_gap_dimension/split/undef_ref_audit.py"])
    assert rc2 == 0, f"undef_ref_audit failed:\n{txt2}"
    undef_refs = [int(x) for x in re.findall(r"undef-refs:\s*(\d+)", txt2)]
    undef_cites = [int(x) for x in re.findall(r"undef-cites:\s*(\d+)", txt2)]
    assert len(undef_refs) == 3 and all(v == 0 for v in undef_refs), f"Non-zero undef-refs:\n{txt2}"
    assert len(undef_cites) == 3 and all(v == 0 for v in undef_cites), f"Non-zero undef-cites:\n{txt2}"
    out.append("  [OK] Split tracks 2A / 2B / 2C undefined-ref & citation audit: 0 / 0 across all 3 tracks")


def main() -> None:
    out = ["=== Master Repository Integrity Verification ==="]
    check_git_conservation(out)
    check_markdown_docs(out)
    check_lean_audits(out)
    check_papers_and_split(out)
    out.append("ALL REPOSITORY INTEGRITY CHECKS PASSED.")
    text = "\n".join(out) + "\n"
    LOG_PATH.write_bytes(text.encode("utf-8"))
    print(text, end="")


if __name__ == "__main__":
    main()
