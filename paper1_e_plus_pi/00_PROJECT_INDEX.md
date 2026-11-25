# e+π Project Index (2026-11-21, English naming)

## Directory layout

```
paper1_e_plus_pi/
├── 01_main_paper/           paper1_e_plus_pi.tex / .pdf (Nov-21 e.html-review revision, 72 pp) + assemble_restructure.ps1
├── 02_companion_paper/      Phase2_revised.tex / .pdf (Nov-21 §6 split + 5 proof-gap completions, 65 pp)
├── 03_submission_prep/      cover-letter draft, journal policy notes, checklists
├── 04_formalization_audits/ Lean working copies (authoritative build in ../../epi_formal/), audit logs, old_build_logs/
├── 05_research_process/     all research branches (A–E rounds, round10_advance, theorem_deepening,
│                            research_continuation, golden_finite_spectrum, spectrum_density_cubic_root_frequency,
│                            window_factorial_frequency, sharp_amplitude_interval_counting,
│                            orbit_intersection_finite_state_frequency, antigravity-takeover, integration)
│                            + Parallel_Research_Plan.md, merge_lean_audit.txt
├── 06_historical_versions/  main_backups · rounds_04_08 · archive_snapshots (zips + papers_old + submission
│                            snapshots + pre_revision_snapshots) · reference_docs
├── 07_research_log_and_guide/ separated scholarly trial logs & inventory (MASTER_INVENTORY_LIST.md,
│                              PAPER1_ATTACK_AND_TRIAL_LOG.md, trial_notes_M1_M2_20261125.md, MASTER_GUIDE_SKILL.md)
└── 00_PROJECT_INDEX.md / 00_research_status.md / 00_merge_review.md
```

## Entry points

| Entry | Content |
| --- | --- |
| [Main paper PDF](01_main_paper/paper1_e_plus_pi.pdf) · [TeX](01_main_paper/paper1_e_plus_pi.tex) | Nov-21 restructure per e.html review: §8 split into §3–§7, new title *Continued-Fraction Windows…*, de-logged, 72 pp (subsequently expanded to 75 pp with Arb exclusion). |
| [Research Log & Master Inventory](07_research_log_and_guide/PAPER1_ATTACK_AND_TRIAL_LOG.md) | Separated trial log, [20-row Master Inventory](07_research_log_and_guide/MASTER_INVENTORY_LIST.md), [M1/M2 notes](07_research_log_and_guide/trial_notes_M1_M2_20261125.md), and [Commander Guide](07_research_log_and_guide/MASTER_GUIDE_SKILL.md). |
| [Companion PDF](02_companion_paper/Phase2_revised.pdf) · [TeX](02_companion_paper/Phase2_revised.tex) | Nov-21: §6 split into three top-level sections, five proof gaps completed, SharpWindow boundary stated, references cleaned, 65 pp. |
| [Research status](00_research_status.md) | theorem placement, route progress, missing lemmas, re-check records. |
| [Merge review](00_merge_review.md) | write-in markers, axiom audits, recomputation, literature cross-checks. |
| [Research plan](05_research_process/Parallel_Research_Plan.md) | branch records in `05_research_process/`, stage deltas in `06_historical_versions/rounds_04_08/`. |
| [Golden spectrum + Lean](05_research_process/golden_finite_spectrum/README.md) | algorithm, check scope, reproduction commands; [audit log](05_research_process/golden_finite_spectrum/核查与变更记录.md). |
| [Window / factorial / frequency](05_research_process/window_factorial_frequency/) | exact certificates, Lean sources, itemized audits. |
| [Orbit intersection & finite-state frequency](05_research_process/orbit_intersection_finite_state_frequency/) | exact certificates, Lean sources, audits. |
| [Spectrum density & cubic-root frequency](05_research_process/spectrum_density_cubic_root_frequency/) | exact certificates, Lean sources, audits. |
| [Sharp amplitude & interval counting](05_research_process/sharp_amplitude_interval_counting/) | recomputation, Lean sources (SharpWindow.lean), audits. |
| [Handoff & reproduction](05_research_process/antigravity-takeover/) | branch progress, verification packages. |
| [Archive snapshots](06_historical_versions/archive_snapshots/pre_revision_snapshots/) | all prior ZIP deliveries; older tex builds in `archive_snapshots/papers_old/`; past review documents in `reference_docs/`. |
| [Pre-restructure backup](06_historical_versions/main_backups/paper1_e_plus_pi.backup_20261121.tex) | the 4,596-line version before the Nov-21 restructure. |

## Related locations (workspace root)

- `epi_formal/` — authoritative Lean 4 project (04_formalization_audits holds working copies only); do not restructure internally.
- `verification/` — project-wide verification records and scripts (Chinese record filenames kept as frozen process logs).
- `paper2_spectral_gap_dimension/` — current paper 2 tex/pdf + `historical_versions/`.
- `progress_and_path_analysis.md`, `AGENTS.md` — workspace-level notes and discipline.
- `reorganize_step1_20261121.ps1`, `reorganize_step2_20261121.ps1`, `rename_english_20261121.ps1` — the consolidation and English-rename scripts (conservation-checked, zero deletions).
- `scripts/` — auto-generated tooling probes (paper-search MCP), not project content.

> Note — historical process records (files inside `05_research_process/`, `06_historical_versions/rounds_04_08/`, `verification/`) keep their original mostly-Chinese **filenames** by design, so their internal cross-references remain valid; all **directories** and all current-paper files use English names. Old paths (`第二阶段修订/`, `parallel_work/`, `历史归档/`, `01_主稿/`, …) map to `02_companion_paper/`, `05_research_process/`, `06_historical_versions/archive_snapshots/pre_revision_snapshots/`, `01_main_paper/`, … respectively.
