# E7 验收检查（2026-11-24）：三篇 frontmatter v2 草案
# 检查项（任务书 E7 验收）：标题<=16词；摘要<=200词；配对花括号；
# 两处占位句原文精确出现；e+pi 免责句；companion 句。
import re, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPLIT = ROOT / "paper2_spectral_gap_dimension" / "split"
FILES = {
    "2A": SPLIT / "frontmatter-2A-v2.tex",
    "2B": SPLIT / "frontmatter-2B-v2.tex",
    "2C": SPLIT / "frontmatter-2C-v2.tex",
}
PH_2B = "[Unified structural-alphabet theorem: to be inserted]"
PH_2C = "[Critical scaling theorem: to be inserted]"
EPI  = r"does not resolve the open problem of the irrationality of $e+\pi$"
COMP = "The full 63-page version containing all proofs is available as a companion manuscript."

def strip_comments(s: str) -> str:
    return re.sub(r"(?<!\\)%.*", "", s)

def brace_report(s: str) -> str:
    t = s.replace(r"\{", "").replace(r"\}", "").replace("\\\\", "")
    bal, minbal, line = 0, 0, 1
    for ch in t:
        if ch == "\n":
            line += 1
        elif ch == "{":
            bal += 1
        elif ch == "}":
            bal -= 1
            if bal < minbal:
                minbal = bal
    return f"final_balance={bal} min_balance={minbal}"

for key, path in FILES.items():
    raw = path.read_text(encoding="utf-8")
    txt = strip_comments(raw)
    norm = " ".join(txt.split())
    m_t = re.search(r"\\title\{(.*?)\}", txt, re.DOTALL)
    m_a = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", txt, re.DOTALL)
    title = m_t.group(1) if m_t else "<MISSING>"
    abstract = m_a.group(1) if m_a else "<MISSING>"
    tw = len(title.split())
    aw = len(abstract.split())
    print(f"== {key} == {path.name}")
    print(f"title_words={tw} (<=16 required) | title={' '.join(title.split())}")
    print(f"abstract_raw_token_count={aw} (<=200 required)")
    print(f"braces: {brace_report(txt)}")
    print(f"has_begin_document={chr(92)+'begin{document}' in txt} begin/end_abstract={m_a is not None}")
    print(f"placeholder_2B_exact={PH_2B in raw} | placeholder_2C_exact={PH_2C in raw}")
    print(f"epi_phrase: raw={EPI in raw} normalized={EPI in norm}")
    print(f"companion: raw={COMP in raw} normalized={COMP in norm}")
    print()
