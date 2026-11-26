<!-- NON-CANONICAL / DO NOT CITE -->
THM-0003 is formalized in the existing project module `epi_formal/EpiFormal/Classification.lean` (not copied here, to keep one source of truth):
- (A) and its converse: `Classification.theorem2_classification` (l.539): Tendsto (j·‖Q_j x‖) → 0 ↔ x ∈ latticeL
- (B): `Classification.corollary3_gap` (l.679): x ∉ latticeL → ∀ c < 1/4, ¬ eventually j‖Q_j x‖ ≤ c
Audit: `epi_formal/AuditCorollary3Gap.lean`; evidence: `logs/verification/LEAN-THM-0003.log`; CI siege gate entries for both.
