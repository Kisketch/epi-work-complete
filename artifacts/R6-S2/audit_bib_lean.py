# audit_bib_lean.py -- skeptic audit: (1) every bibliographic field of paper_draft.tex against prior_art.md
# (string search, case-insensitive, after normalising dashes); (2) Lean/CI claims of Section sec:lean against
# formal/R6_S2.log, formal/R6_S7.log, formal/R6_S7.lean.  Mechanical only; judgement is in the audit report.
import re, os
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
rd = lambda p: open(os.path.join(ROOT, p), encoding="utf-8").read()
paper = rd("artifacts/R6-S2/paper_draft.tex")
pa = rd("artifacts/R6-S2/prior_art.md").lower().replace("–", "-").replace("—", "-")
d5 = rd("artifacts/THM-0005/paper_draft.tex").lower()

fields = {
 "KL": ["kraaikamp", "liardet", "good approximations and continued fractions", "proc. amer. math. soc", "112",
        "no. 2", "303-309", "1991", "10.1090/s0002-9939-1991-1062392-7"],
 "Larcher": ["larcher", "a convergence problem connected with continued fractions", "103", "no. 3", "718-722", "1988"],
 "BDS": ["biró", "deshouillers", "sós", "good approximation and characterization of subgroups", "studia sci. math. hungar",
         "38", "97-113", "2001", "10.1556/sscmath.38.2001.1-4.7", "real.mtak.hu/110616", "open-access copy read"],
 "Stewart": ["stewart", "irregularities of uniform distribution", "acta math. acad. sci. hungar", "37", "185-221", "1981",
             "10.1007/bf01904883", "remark 3", "reference list"],
 "Komatsu99": ["komatsu", "on inhomogeneous diophantine approximation with some quasi-periodic expressions, ii",
               "nombres bordeaux", "11", "331-344", "1999", "10.5802/jtnb.254", "mr1745883", "zbl 1058.11049"],
 "Kim-Liao (text)": ["1508.00520", "kim", "liao"],
}
print("=== (1) bibliographic fields: found in prior_art.md? (and, if not, in THM-0005 draft?) ===")
for k, fl in fields.items():
    for f in fl:
        inpa = f in pa
        ind5 = f in d5
        print(f"{k:16s} {f!r:70s} prior_art:{'YES' if inpa else 'NO '}  THM-0005:{'yes' if ind5 else 'no'}")
# special: BDS 'Lemma 4.1' and KL 'Theorem 1' status lines in prior_art
for pat in ["lemma 4.1", "theorem 1/1", "remark 3", "全文本会话未打开", "扫描件"]:
    print(f"prior_art contains {pat!r}: {pat in pa}")

print("\n=== (2) Lean / CI claims ===")
s2 = rd("formal/R6_S2.log"); s7 = rd("formal/R6_S7.log"); l7 = rd("formal/R6_S7.lean")
claims = {
 "R6S7 CI run 46011329540 head 65db490": "46011329540 (head 65db490" in s7,
 "R6S2 CI run 46110437346 head 46d1a36": "46110437346 (head 46d1a36" in s2,
 "9399 jobs": "9399 jobs" in s2,
 "toolchain commit eb6cafb7": "eb6cafb7" in s2 and "eb6cafb7" in s7,
}
for c, v in claims.items(): print(f"{c}: {v}")
gate = ["main", "lower", "upper", "S1_all", "S1a", "S1b", "S1c", "S1d", "lemma0", "cor0'", "cstar_ge_quarter_irrational",
        "cstar_only_W'", "nu_bounds", "main_example11", "nu_one_one", "cstar_example11"]
blk = s2[s2.index("## Build 11"):s2.index("## 公理层级（第 4 阶段）")]
found = re.findall(r"'R6S2\.(\S+?)' depends on axioms: \[([^\]]*)\]", blk)
print("Build 11 (AuditR6S2) theorems:", len(found), "; equal to paper's 16-list:", sorted(n for n, _ in found) == sorted(gate))
print("all exactly [propext, Classical.choice, Quot.sound]:", all(ax == "propext, Classical.choice, Quot.sound" for _, ax in found))
g7 = ["prop1", "mstar_ge_half", "cor2_K_ge_two", "cor2_K_eq_one", "nu_ge_half"]
tail7 = s7.split("CI build of record")[-1]
print("R6S7 gate line in log:", tail7.strip()[:200]); print("all 5 names present:", all(n in tail7 for n in g7))
ax7 = dict(re.findall(r"^'R6S7\.([^']+)' depends on axioms: \[([^\]]*)\]", s7, re.M))
print("R6S7 gate axioms:", {n: ax7.get(n) for n in g7})
print("R6S7 theorems with strict subset of axioms:", {n: a for n, a in ax7.items() if a != "propext, Classical.choice, Quot.sound"})
dk = re.findall(r"^theorem (\S+)[^\n]*\n?[^\n]*decide \+kernel", l7, re.M)
print("R6_S7.lean: occurrences of 'decide +kernel':", l7.count("decide +kernel"), "; plain 'by decide' occurrences:",
      len(re.findall(r"by decide\b(?! \+kernel)", l7)))
main_lean = rd("formal/R6_S2_main.lean")
print("R6_S2_main.lean: 'decide +kernel' occurrences:", main_lean.count("decide +kernel"))
for f in ["formal/R6_S2.lean", "formal/R6_S2_blocks.lean", "formal/R6_S2_realize.lean", "formal/R6_S2_localize.lean",
          "formal/R6_S2_main.lean", "formal/R6_S2_audit.lean", "formal/R6_S7.lean"]:
    t = rd(f)
    code = re.sub(r"/-.*?-/", "", t, flags=re.S); code = re.sub(r"--[^\n]*", "", code)
    print(f"{f}: sorry={len(re.findall(r'\\bsorry\\b', code))} admit={len(re.findall(r'\\badmit\\b', code))} "
          f"native_decide={code.count('native_decide')} axiom-decls={len(re.findall(r'^\\s*axiom\\b', code, re.M))} "
          f"'decide +kernel'={code.count('decide +kernel')}")
