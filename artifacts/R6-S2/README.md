# artifacts/R6-S2 — paper draft on R6-S2 (NON-CANONICAL)

**Status:** non-canonical draft, mathematical body only, not for citation or submission. Written 2026-11-28.
**Unrelated to e+π:** nothing here bears on the irrationality of e+π or of π.

## Files

| File | Contents |
|---|---|
| `paper_draft.tex` | amsart LaTeX draft: "Sharp Kraaikamp–Liardet constants for block-Hurwitz continued fractions" |
| `check_tex.py` | static checker: `\ref`/`\label`, `\cite`/`\bibitem`, environment pairing, brace/`$`/`\[ \]` balance, placeholder and NEW-k listing |
| `README.md` | this file |

No TeX was available on the machine, so the draft has **not been compiled**. Run `python3 check_tex.py paper_draft.tex` (last run 2026-11-28, after filling the prior-art section: RESULT OK, 0 errors; 9 warnings, all for section/lemma labels that are never referenced).

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

## Prior art (filled 2026-11-28 from `prior_art.md`)

Subsection `subsec:prior` now follows `prior_art.md` (d):
- W=∅ is a special case of Paper 2 `thm:growing-rec-spectrum` (full spectrum; stronger there) and of THM-0005 (single instance (e−1)/2) / THM-0006 (lower-bound half).
- W=(1,1), α=e is a special case of 2E `thm:full-spectra` (full spectrum); S1(a)'s weight limit matches 2E `thm:full-identities`.
- 2E `thm:even-hurwitz` is only a block-boundary recurrence identity, with no KL constant.
- The general bound 1/4 is KL 1991; only its bibliographic fields were checked in the 2026-11-28 check.
- Komatsu 1999 (JTNB 11(2), 331–344, doi:10.5802/jtnb.254): a different functional (liminf over all q) with related methods. No conversion was found or proved.
- The scope of the negative search is stated, including what was not searched (MathSciNet, zbMATH, full texts of KL / Stewart, Komatsu's theorem formulas, monographs).
- Conclusion: general-W formula, ν(W), the ν<1 examples and c\*≥1/2 are "not found in the literature consulted (a negative search only)". For m\*≥1/2 (R6-S7), no literature search was made; it may restate classical facts about continuants.

## Revision after the isolated audit (2026-11-28, VERDICT MINOR_FIX)

All 14 audit items and the 3 overfull boxes reported by the Colab trial compile (commit 7860a03: 18 pages, 0 errors, 0 undefined references) were addressed in `paper_draft.tex`. No mathematical content was changed. The changes are:
- bibliography notes: Larcher, BDS and Stewart;
- formalization status of [D5] Prop. 9;
- negative-search coverage (located-but-unopened items; Bourla listed separately);
- the "all cases other than W=∅ and α=e" wording;
- the Komatsu attribution;
- the NEW-1 citations;
- "conditional on the expansion of e";
- the `decide +kernel` naming;
- "CI records; builds not re-run" in the abstract and introduction;
- "for K(W)≥2" in the abstract;
- the category labels;
- the ν((…)) notation;
- separate Theorem A/B environments, with no duplicate lemma names;
- the wording of "β fixed" in Section 5;
- the NEW-5 items added to the unaudited list;
- the overfull boxes (display for the long word, `align*` for the Lean statement, display for the axiom list).

The NEW-k items keep their "not independently audited" labels in the text. The audit found NEW-1..4 correct; whether to relabel them is left to the coordinator.

## Remaining placeholders

- `% PLACEHOLDER-BIB` (Section 3, "Standard facts", and end of bibliography): a textbook reference for (F1)–(F3). Not verified.
- `% PLACEHOLDER-BIB` (Example `ex:e` and end of bibliography): a verified original source for the expansion e=[2;1,2,1,1,4,1,1,6,…]. Not verified.
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
- Prior-art check is a negative search only (see `subsec:prior`); MathSciNet/zbMATH not searched; no search for m\*≥1/2.
- Lean builds were not re-run for this draft; CI run numbers and axiom lists are quoted from formal/R6_S2.log and formal/R6_S7.log.
