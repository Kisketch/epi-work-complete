<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Cross-round memory (siege campaign)
- R1: Workers converge on the same wall for N6 (P1 ⇔ ℚ-independence of 1, e, π). Every route fails at "no tool controls a linear relation between e and π". Do not re-run blind N6 waves without a new concrete missing lemma (premature-convergence risk).
- R1: Workers' scratchpad scripts collide (shared a.py / c.py). Require unique filenames per worker and copy scripts into logs/verification immediately (missing certificate × 1).
- R1: The Lean gate is blocked by the filesystem (mmap/permission on the Windows mount). Fix the environment before scheduling formalizer work.
- R1: Paper 1 proofs are sound but terse; checkers find only expository gaps. Repair queues are cheap wins.
- R2: Session restarts kill background agents and long builds. Resume agents with SendMessage; run lake builds in ≤ 590 s foreground chunks (lake resumes incrementally).
- R2: The native-filesystem copy (~/epi_native) plus `lake exe cache get` fixes the Windows-mount olean failure. Each module takes ~5 min, so use module-targeted builds.
- R2: Literature workers hit AMS 403. The classical rigidity lemma (Kraaikamp–Liardet 1991) is reachable only via secondary statements in Conze et al.; human PDF retrieval is needed.
- R2: Workers can produce genuine small new results when the query is a sharp finite question (κ exact value). Prefer such queries over blind attacks on N6.
- R3: GitHub CI (16 GB, full `lake build` + siege axiom gate) is the reliable Lean build of record; the local machine (~2.5 GB free with the browser open) cannot import Mathlib within 590 s.
- R3: Always grep existing declarations before formalizing: THM-0003(A) already existed as theorem2_classification.
- R3: Never mass-sed across logs/: ledgers and handoffs are append-only.
- R4: Standalone Lean modules with narrow Mathlib imports check locally in ~90 s; use them for new formalization, with CI as the build of record.
