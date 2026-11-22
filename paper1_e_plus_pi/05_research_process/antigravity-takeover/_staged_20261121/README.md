# e+pi consolidated papers

The current TeX sources are 01_Paper/paper.tex and 02_Companion/Phase2_revised.tex.
Run pdfLaTeX three times on each file for stable cross-references. The PDFs
are supplied separately. The Chinese research map is 00_当前研究路径与进度.md.
The other dated research notes document earlier stages.

From parallel_work/golden_finite_spectrum run golden_finite_spectrum.py,
quadratic_phase_certificate.py, and verify_ten_rounds.py with Python 3.
The first two use standard-library rational arithmetic. The high-precision
Case 2 regression in Certificates needs mpmath.

The Lean source excerpts use the project's Lean 4.35.0 and mathlib v4.35.0
environment. For example, run lake env lean EpiFormal/GeneralEndpointRigidity.lean
from the project's epi_formal root, and Audit.lean for the full audit.
The Audit directory records the original per-declaration outputs. Some
declarations explicitly depend on external mathematical facts.

The latest round uses verify_research_advance.py from the same certificate
folder and ResearchAdvance.lean from the Lean project environment.

The trace and finite-state extension is reproduced by verify_trace_markov.py
in the certificate folder, and TraceMarkov.lean in the Lean project environment.

The density and cubic-root extension is reproduced by verify_density_cube.py
in the certificate folder, and DensityCube.lean in the Lean project environment.

The sharp amplitude and uniform-window checks use verify_sharp_window.py
in the certificate folder, and SharpWindow.lean in the Lean project environment.

The takeover source overlays, current axiom audit and verification commands are in Takeover/.
