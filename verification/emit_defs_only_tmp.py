"""Extract defs-only prefix of the generated data file for a fast elaboration test."""
src = "epi_formal/EpiFormal/ResidueCertData41179_Draft.lean"
dst = "epi_formal/EpiFormal/ResidueCertData41179_DefsOnly_Draft.lean"
t = open(src, encoding="utf-8").read()
i = t.index("/-- Cellwise upper bounds")
open(dst, "w", encoding="utf-8", newline="").write(t[:i] + "/- defs only -/\n")
print("wrote defs-only, bytes:", len(t[:i]))
