# Companion Paper 2E: Full Regular Convergent Spectra of $e$, Signed Hurwitz Recurrences, and Brouwer-Free Perron--Frobenius Elimination

> Isolation guarantee: this spin-off package sits outside the core 11 slices of [`../split/src_sections/`](../split/src_sections/) while its machine-checked results are cleanly cited in the main Paper~2 verification summary (`patch_round2_20261125.py`). Strictly follows [`../../AGENTS.md`](../../AGENTS.md): **does not address the irrationality of $e+\pi$.**

## Contents

- [`paper2E_full_convergent_and_even_hurwitz.tex`](paper2E_full_convergent_and_even_hurwitz.tex) / [`.pdf`](paper2E_full_convergent_and_even_hurwitz.pdf): 8-page standalone manuscript (`0` LaTeX errors, `0` undefined refs, `0` Overfull `\hbox`; `verify_refs.py` `2 ok, 0 warn, 0 fail`).
- **Lean 4 formalization (`53` standalone audited declarations, base axioms only, `sorryAx = 0`)**:
  - [`../../epi_formal/EpiFormal/FullConvergentSpectrum.lean`](../../epi_formal/EpiFormal/FullConvergentSpectrum.lean) & [`../../epi_formal/AuditFullConvergentSpectrum.lean`](../../epi_formal/AuditFullConvergentSpectrum.lean) (`40` declarations -> [`../../verification/audit_full_convergent_spectrum_20261125.log`](../../verification/audit_full_convergent_spectrum_20261125.log))
  - [`../../epi_formal/EpiFormal/PerronFrobenius.lean`](../../epi_formal/EpiFormal/PerronFrobenius.lean) & [`../../epi_formal/AuditPerronFrobenius.lean`](../../epi_formal/AuditPerronFrobenius.lean) (`13` declarations -> [`../../verification/audit_perron_frobenius_20261125.log`](../../verification/audit_perron_frobenius_20261125.log), discharging R3)
- **Numerical & adversarial verification (Category 4)**:
  - [`../../verification/verify_mobius_e_full_conv_20261125.py`](../../verification/verify_mobius_e_full_conv_20261125.py) / [`.log`](../../verification/verify_mobius_e_full_conv_20261125.log)
  - [`../../verification/verify_nonlinear_blr_20261125.py`](../../verification/verify_nonlinear_blr_20261125.py) / [`.log`](../../verification/verify_nonlinear_blr_20261125.log)
  - [`../../verification/kahane_and_blr_audit_20261125.md`](../../verification/kahane_and_blr_audit_20261125.md)

## Reproduction

```powershell
# Lean 4 build & axiom audits (from repo root)
Set-Location epi_formal
lake build EpiFormal.FullConvergentSpectrum EpiFormal.PerronFrobenius
lake env lean AuditFullConvergentSpectrum.lean
lake env lean AuditPerronFrobenius.lean
Set-Location ..

# Clean 3-pass PDF build & ref verification
Set-Location paper2_spectral_gap_dimension\spinoff_full_convergent_and_even_hurwitz_20261125
pdflatex -interaction=nonstopmode paper2E_full_convergent_and_even_hurwitz.tex
pdflatex -interaction=nonstopmode paper2E_full_convergent_and_even_hurwitz.tex
pdflatex -interaction=nonstopmode paper2E_full_convergent_and_even_hurwitz.tex
Set-Location ..\..
py .agents\skills\mathodology-evidence-search\scripts\verify_refs.py paper2_spectral_gap_dimension\spinoff_full_convergent_and_even_hurwitz_20261125\paper2E_full_convergent_and_even_hurwitz.tex
```
