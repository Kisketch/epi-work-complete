# audit_tex.py -- skeptic audit: runs check_tex.py on the draft, simulates amsart theorem numbering of the draft
# and of artifacts/THM-0005/paper_draft.tex (to check "Proposition 9" / "Theorem 1" of [D5]), and lists
# notational inconsistencies for words W written as \nu(...) .  Mechanical only.
import re, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
print(subprocess.run([sys.executable, os.path.join(HERE, "check_tex.py"), os.path.join(HERE, "paper_draft.tex")],
                     capture_output=True, text=True).stdout.splitlines()[-1])

def numbering(path, per_section):
    src = open(path, encoding="utf-8").read()
    envs = ("theorem", "proposition", "corollary", "lemma", "definition", "example", "remark")
    sec = 0; cnt = 0; out = []
    for m in re.finditer(r"\\section\{|\\begin\{(" + "|".join(envs) + r")\}(\[[^\]]*\])?(\s*\\label\{([^}]*)\})?", src):
        if m.group(0).startswith("\\section"):
            sec += 1
            if per_section: cnt = 0
            continue
        cnt += 1
        line = src.count("\n", 0, m.start()) + 1
        num = f"{sec}.{cnt}" if per_section else f"{cnt}"
        out.append((num, m.group(1), m.group(4), line))
    return out
print("\n--- draft numbering (amsart, [section]) ---")
for n, e, lab, line in numbering(os.path.join(HERE, "paper_draft.tex"), True):
    print(f"{e:12s} {n:6s} {lab or '':18s} line {line}")
print("\n--- THM-0005 numbering (global counter) ---")
for n, e, lab, line in numbering(os.path.join(ROOT, "artifacts/THM-0005/paper_draft.tex"), False):
    print(f"{e:12s} {n:4s} {lab or '':16s} line {line}")
src = open(os.path.join(HERE, "paper_draft.tex"), encoding="utf-8").read()
print("\n--- \\nu applied to explicit words (notation consistency) ---")
for m in sorted(set(re.findall(r"\\nu\((\(?[0-9, ]+\)?)\)", src))): print("  \\nu(" + m + ")")
