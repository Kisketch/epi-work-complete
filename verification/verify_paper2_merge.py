from pathlib import Path
import csv
import re

ROOT = Path(__file__).resolve().parent.parent
DRAFT_B_CANDIDATES = [
    ROOT / "paper1_e_plus_pi" / "02_companion_paper" / "Phase2_revised.tex",
    ROOT / "papers" / "historical_draft_B_Phase2_revised" / "Phase2_revised.tex",
]
MERGED_CANDIDATES = [
    ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex",
    ROOT / "papers" / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex",
]
DRAFT_B_PATH = next((p for p in DRAFT_B_CANDIDATES if p.exists()), DRAFT_B_CANDIDATES[0])
MERGED_PATH = next((p for p in MERGED_CANDIDATES if p.exists()), MERGED_CANDIDATES[0])
LOG_PATH = ROOT / "verification" / "verify_paper2_merge.log"

def main():
    merged = MERGED_PATH.read_text(encoding="utf-8")
    draft_lines = len(DRAFT_B_PATH.read_text(encoding="utf-8").splitlines()) if DRAFT_B_PATH.exists() else None

    out = []
    out.append("=== Paper 2 Merge & Integrity Verification ===")
    out.append(f"Paper 2 source: {MERGED_PATH.relative_to(ROOT).as_posix()} ({len(merged.splitlines())} lines)")
    if draft_lines is not None:
        out.append(f"Historical B draft: {DRAFT_B_PATH.relative_to(ROOT).as_posix()} ({draft_lines} lines)")

    # 1. Labels & Refs
    labels = re.findall(r"\\label\{([^}]+)\}", merged)
    refs = re.findall(r"\\(?:eq)?ref\{([^}]+)\}", merged)
    dups = sorted({x for x in labels if labels.count(x) > 1})
    undef_refs = sorted(set(refs) - set(labels))
    assert not dups, f"Duplicate labels: {dups}"
    assert not undef_refs, f"Undefined refs: {undef_refs}"
    out.append(f"Labels: {len(labels)} (all unique); Undefined refs: 0")

    # 2. Citations & Bibitems
    cites = []
    for c in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", merged):
        cites.extend([x.strip() for x in c.split(",")])
    bibs = re.findall(r"\\bibitem\{([^}]+)\}", merged)
    missing_bibs = sorted(set(cites) - set(bibs))
    uncited_bibs = sorted(set(bibs) - set(cites))
    assert not missing_bibs, f"Missing bibitems: {missing_bibs}"
    assert not uncited_bibs, f"Uncited bibitems: {uncited_bibs}"
    out.append(f"Bibitems: {len(bibs)}/{len(bibs)} (100% cited in body, 0 missing)")

    # 3. Brace & Environment balance
    # Strip escaped braces \{ \}
    clean = merged.replace(r"\{", "").replace(r"\}", "")
    open_b = clean.count("{")
    close_b = clean.count("}")
    assert open_b == close_b, f"Unbalanced braces: {open_b} vs {close_b}"
    begins = re.findall(r"\\begin\{([^}]+)\}", merged)
    ends = re.findall(r"\\end\{([^}]+)\}", merged)
    assert len(begins) == len(ends), f"Unbalanced environments: {len(begins)} vs {len(ends)}"
    out.append(f"Braces balanced ({open_b}); Environments balanced ({len(begins)})")

    # 4. Proof sketch stub check (must be 0 unfinished theorem-stub headers)
    sketches = re.findall(
        r"(?:\\begin\{proof\}\[[^\]]*sketch[^\]]*\]|\\(?:paragraph|emph|textbf)\{Proof\s+sketch\}|Proof\s+sketch\.)",
        merged,
        flags=re.IGNORECASE,
    )
    assert not sketches, f"Found residual Proof sketch stub: {sketches}"
    out.append("Residual 'Proof sketch' stubs: 0")

    # 4b. Byte-for-byte slice concatenation check against slice_index.csv
    slice_dir = MERGED_PATH.parent / "split" / "src_sections"
    slice_csv = slice_dir / "slice_index.csv"
    with open(slice_csv, encoding="utf-8-sig") as f:
        slice_rows = list(csv.DictReader(f))
    joined_bytes = b"".join((slice_dir / row["File"]).read_bytes() for row in slice_rows)
    main_bytes = MERGED_PATH.read_bytes()
    assert joined_bytes == main_bytes, (
        f"Slice concatenation mismatch: {len(joined_bytes)} vs {len(main_bytes)} bytes"
    )
    out.append(f"Slice concatenation byte-for-byte match ({len(slice_rows)} files, {len(main_bytes)} bytes): OK")

    # 5. Content completeness checks (Desktop + Prior Workspace + Extensions)
    norm_merged = re.sub(r"\\allowbreak\{\}|\\allowbreak\s*", "", merged)
    items = [
        ("Desktop: Author placeholder", "Author name"),
        ("Desktop: KL 2*Lambda(x) normalization", r"2\Lam(x)"),
        ("Desktop: Lemma A", r"\begin{lemmaA}"),
        ("Desktop: Theorem 1 Classification", r"\label{thm:class}"),
        ("Desktop: Theorem 2 Gap", r"\label{thm:gap}"),
        ("Desktop: Remark 4 (1,e,pi linear indep.)", r"\label{rem:linear-indep}"),
        ("Desktop: GaugeNull.mkMetric_strictLevel_null", "mkMetric\\_strictLevel\\_null"),
        ("Desktop: Cor 14 Exact critical gauge", r"\label{cor:exact-gauge}"),
        ("Desktop: Remark 15 level separation", r"\label{rem:gauge-scale}"),
        ("Desktop: Numerical box-counting 0.371..0.446", "0.371"),
        ("Desktop: Numerical Caveat 10^{60}", "10^{60}"),
        ("Desktop: Use of AI section", "Use of AI and formal verification"),
        ("Workspace: Full spectrum 1/4 Z", r"\frac14\Z_{\ge0}\cup\{\infty\}"),
        ("Workspace: Trichotomy", r"\label{thm:trichotomy}"),
        ("Workspace: General cj+d", r"\label{thm:general-rec}"),
        ("Workspace: WeightedExactDim", "WeightedExactDim"),
        ("Workspace: Hermite windows", r"\label{thm:windows}"),
        ("Workspace: Short windows a.e.", r"\label{thm:short-ae}"),
        ("Workspace: Divergent windows", r"\label{thm:no-short-dim}"),
        ("Workspace: Residues 357/512 < dim < 179/256", "357/512"),
        ("Workspace: Residues upper 179/256 (N=512)", "179/256"),
        ("Workspace: 512 cells & N=2^{80}", "2^{80}"),
        ("Workspace: Margins 48/10000 & 27/100000", "48/10000"),
        ("Workspace: Lipschitz 10/3 & 40/3", "40/3"),
        ("Workspace: residue_certificate_general_N512.py", "residue\\_certificate\\_general\\_N512.py"),
        ("Workspace: ResidueCertTable", "ResidueCertTable"),
        ("Workspace: General modulus m=2..6 thm", r"\label{thm:residues-general}"),
        ("Workspace: Table residues-general", r"\label{tab:residues-general}"),
        ("Workspace: WindowShortAeRealize", "WindowShortAeRealize"),
        ("Workspace: ResidueModGeneral", "ResidueModGeneral"),
        ("Workspace: TransferOperatorDim", "TransferOperatorDim"),
        ("Workspace: FiniteStateComplete", "FiniteStateComplete"),
        ("Workspace: ResidueAsymptotic", "ResidueAsymptotic"),
        ("Workspace: GeneralGrowingRec", "GeneralGrowingRec"),
        ("Workspace: GeneralGrowingDim", "GeneralGrowingDim"),
        ("Workspace: Thm residues-asymptotic", r"\label{thm:residues-asymptotic}"),
        ("Workspace: Thm growing-rec-spectrum", r"\label{thm:growing-rec-spectrum}"),
        ("Workspace: Thm growing-rec-dim-phase", r"\label{thm:growing-rec-dim-phase}"),
        ("Workspace: Cor growing-rec-three-regimes", r"\label{cor:growing-rec-three-regimes}"),
        ("Workspace: verify_paper2_extensions.py", "verify\\_paper2\\_extensions.py"),
        ("Workspace: Audit 937 declarations", "937"),
        ("Workspace: Thm multi-residue-asymptotic", r"\label{thm:multi-residue-asymptotic}"),
        ("Workspace: Table multi-residue-asymptotic", r"\label{tab:multi-residue-asymptotic}"),
        ("Workspace: ResidueMultiAsymptotic", "ResidueMultiAsymptotic"),
        ("Workspace: AuditResidueMultiAsymptotic", "AuditResidueMultiAsymptotic"),
        ("Workspace: verify_residue_multi_asymptotic.py", "verify\\_residue\\_multi\\_asymptotic.py"),
    ]
    for label, pat in items:
        found = pat in norm_merged
        assert found, f"Missing item: {label} ({pat})"
        out.append(f"  [OK] {label}")

    out.append("ALL MERGE & INTEGRITY CHECKS PASSED.")
    text = "\n".join(out) + "\n"
    with open(LOG_PATH, "w", encoding="utf-8") as f:
        f.write(text)
    print(text)

if __name__ == "__main__":
    main()
