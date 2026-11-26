<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Previous Research Summary (Phase 0 inventory, 2026-11-25)

Commander inventory compiled from files actually present in this worktree (HEAD ffcd38d). Items not verified this session are marked TODO / BLOCKED.

## 1. P1: the final target of Paper One
Source: `paper1_e_plus_pi/01_main_paper/paper1_e_plus_pi.tex` §`sec:lean-reduction` (l.4515–4596) and Lean `epi_formal/EpiFormal/EscapeReduction.lean` (`def P1`, l.~346).

- L := ℤ + ℤ·(e+1)/2.
- **P1: ∀ B ≥ 1, Bπ ∉ L.**
- Kernel-checked (author's records, **re-run not reproduced this session**): `reduction_to_lattice`, `P1_imp_irrational : P1 → Irrational (e+π)`.
- Proved on paper only (Prop. `prop:rational-span`): ⋃_B B⁻¹L = ℚ+ℚe. Hence **P1 ⇔ 1, e, π are linearly independent over ℚ**.
- Honest status (AGENTS.md §4): P1 is a famous open problem. It implies the irrationality of e+π, e−π and π/e, each of which is open. It is **not** a reduction in difficulty. Paper 1 itself labels it "a change of target, not a reduction in difficulty".

## 2. Existing results (per repo records)
- Paper 1: window-count periodicity for rational e+x, affine classification, golden-orbit spectra for B=1..6 plus multiscale targets, and the eventual-dimension theorem `thm:eventual-dimension` (on paper; "historical Lean records refer to earlier declarations"). Plus a feasibility audit of 8 routes, all negative.
- Paper 2 / 2D / 2E: spectral-gap and dimension results, μ(e)=2, and the full convergent spectrum of e. The README claims 1,093 audited declarations, sorryAx=0. Those Lean claims are **author-reported, not re-run this session**.

## 3. Failed or eliminated routes (Paper 1 §feasibility)
Quantitative gap (uniform already); Baker linear forms (e is not a known logarithm); CF structure of π (no handle); π-representations; integral positivity (wrong direction); Nesterenko mining (7 paths fail); period/E-G (conditional only); literature 2024–26 (nothing supplies the input).

## 4. Lean assets / toolchain
- `epi_formal/lean-toolchain` = leanprover/lean4:v4.35.0; mathlib rev v4.35.0. elan/lake are installed at ~/.elan/bin.
- **BLOCKED (2026-11-25)**: there is no `.lake` in this worktree, and symlinks are not supported on this filesystem. `lake env lean` against the main checkout's `.lake` fails with `failed to open file .../Mathlib/...olean|.ir: Operation not permitted`. The cause is likely mmap restrictions on the Windows-mounted volume. The Lean gate therefore cannot be run this session.

## 5. Draft status
Paper 1 (75 pp), Paper 2 (66 pp), 2D (18 pp), 2E (8 pp) according to the README. TODO: recompile not attempted this session.

## 6. Open issues / next steps
- P1 is open (the core).
- Rational-span proposition is not formalized → candidate THM unit.
- thm:eventual-dimension has no current Lean declaration matching the revised statement → candidate THM unit.
- Lean environment unblock (copy or rebuild `.lake` on a native filesystem).
