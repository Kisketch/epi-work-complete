import os

BASE = "epi_formal"
EPI = os.path.join(BASE, "EpiFormal")

have = set(f[:-5] for f in os.listdir(EPI) if f.endswith(".lean"))

drafts = {
    "2A": os.path.join(BASE, "EpiFormal2A_Draft.lean"),
    "2B": os.path.join(BASE, "EpiFormal2B_Draft.lean"),
    "2C": os.path.join(BASE, "EpiFormal2C_Draft.lean"),
}

ok = True
for name, path in drafts.items():
    want = []
    for line in open(path, encoding="utf-8"):
        s = line.strip()
        if s.startswith("import EpiFormal."):
            want.append(s.split("import EpiFormal.")[1].strip())
    missing = [w for w in want if w not in have]
    print(name, "imports:", len(want), "missing:", missing)
    if missing:
        ok = False

print("main entry imports:",
      sum(1 for l in open(os.path.join(BASE, "EpiFormal.lean"), encoding="utf-8")
          if l.strip().startswith("import ")))
print("submodules on disk:", len(have))
print("ALL-EXIST" if ok else "MISSING-FOUND")
