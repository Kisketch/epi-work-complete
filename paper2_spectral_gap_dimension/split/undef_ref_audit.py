import re

tracks = [
    "2A_core_gauge_trichotomy",
    "2B_general_theory",
    "2C_windows_residues_finstate",
]
for t in tracks:
    log = open(
        "paper2_spectral_gap_dimension/split/" + t + "/build/paper2"
        + t[1] + "_draft.log",
        encoding="utf-8",
        errors="replace",
    ).read()
    refs = sorted(set(re.findall(r"Reference `([^']+)' on page", log)))
    cites = sorted(set(re.findall(r"Citation `([^']+)' on page", log)))
    print("=== " + t + " ===")
    print("undef-refs:", len(refs))
    for r in refs:
        print("  ref:", r)
    print("undef-cites:", len(cites))
    for c in cites:
        print("  cite:", c)
