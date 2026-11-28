# artifacts/R6-S2 — paper draft on R6-S2 (NON-CANONICAL)

**Status:** non-canonical draft, mathematical body only, not for citation or submission. Written 2026-11-28.
**Unrelated to e+π:** nothing here bears on the irrationality of e+π or of π.

## Files

| File | Contents |
|---|---|
| `paper_draft.tex` | amsart LaTeX draft: "Sharp Kraaikamp–Liardet constants for block-Hurwitz continued fractions" |
| `check_tex.py` | static checker: `\ref`/`\label`, `\cite`/`\bibitem`, environment pairing, brace/`$`/`\[ \]` balance, placeholder and NEW-k listing |
| `README.md` | this file |

No TeX was available on the machine, so the draft has **not been compiled**. Run `python3 check_tex.py paper_draft.tex` (last run: RESULT OK, 0 errors; 9 warnings, all for section/lemma labels that are never referenced).

## Results in the draft and where they come from

| Draft | Content | Source (only these) | Status in the project |
|---|---|---|---|
| Thm A (`thm:A`) | c\*(α)=ν(W), attained; depends only on W; 1/4 ≤ ν ≤ 1 | PLAN_GRAPH.md S.2 R6-S2; proofs/R6-S2.md v2 §2–§7 | L3_FORMALIZED (CI 46110437346) |
| Lemma S1 (`lem:S1`) | localization (a)–(d) | PLAN_GRAPH.md S.2 R6-S1; proofs/R6-S2.md §5 | L3_FORMALIZED (CI 46110437346) |
| Thm B (`thm:B`) | m\* ≥ 1/2; ν=min(1,m\*) (K≥2), ν=1 (K=1) | PLAN_GRAPH.md row R6-S7; proofs/R6-S7-mstar.md | L3_FORMALIZED (CI 46011329540) |
| Cor `cor:half` | c\* ≥ 1/2 on the block-Hurwitz class | Thm A + Thm B | not a separate Lean theorem (composition of `R6S2.main` and `R6S7.nu_ge_half`) |
| §8.2 numerics | ν(5,1,5)=5/6, ν(5,1,1,1,5)=12/17, 5890-word table, etc. | experiments/R6-S2/*.out (scripts named in the text) | category 4 (finite exact computation) |

`proofs/R6-S2-remarks.md` was **not** used (it is marked "not audited, must not be cited").
The older draft `artifacts/THM-0005/paper_draft.tex` is used for style, for the four checked bibliography entries (KL, Larcher, BDS, Stewart, with their original notes), and for its Proposition 9 (expansion of (e−1)/2) as an input.

## Placeholders (to be filled after the prior-art check)

- `% PLACEHOLDER-PRIOR-ART` — Subsection "Prior art and novelty" (`subsec:prior`). It contains only a neutral sentence; the word "new" is not used for the results.
- `% PLACEHOLDER-BIB` (two places) — a textbook reference for the standard facts (F1)–(F3), and further bibliography from the prior-art check (e.g. Komatsu 1999; a verified source for the expansion of e).
- Author data, MSC codes and keywords (`TODO before submission`).

## Material written for this draft (NOT audited; marked NEW-k in the source)

- **NEW-1** Remark `rem:theta-conv`: for n ≥ 1, θ_n = q_n‖q_nα‖ (agreement with KL's normalisation).
- **NEW-2** Example `ex:calib`: ν((1,1))=1 computed from Thm B(ii). (The value itself is also the Lean theorem `R6S2.nu_one_one`.)
- **NEW-3** Proposition `prop:W-empty` and its proof: for α=(e−1)/2 (W=∅, N=1, A_k=4k+2), c\*(α)=1, 4j+2 < 1/θ_j < 4j+4, limsup_j j‖Q_j z‖ = K_α(z)/4, hence κ=1/4 attained (agreement with THM-0005). Uses THM-0005 draft Prop. 9(ii) as input. Remark `rem:W-empty` comments on it.
- **NEW-4** Example `ex:e`: c\*(e)=1, **conditional** on the classical expansion e=[2;1,2,1,1,4,1,1,6,…] (not proved, source not verified).
- **NEW-5** Editorial additions requested by the v2 audit (D(m,−1)=q_m in Lemma D3; "for k=1 the sum is empty" in (d3)) and Remark `rem:lean-route` (comparison with the Lean proof route, taken from formal/R6_S2_blueprint.md §7.3).

Condensations of the source proofs are marked with `% SRC: <file> <section>` comments for auditors.

## Not done

- Not compiled (no TeX on this machine).
- No independent audit of NEW-1 to NEW-5.
- No prior-art check; novelty undetermined.
- Lean builds were not re-run for this draft; CI run numbers and axiom lists are quoted from formal/R6_S2.log and formal/R6_S7.log.
