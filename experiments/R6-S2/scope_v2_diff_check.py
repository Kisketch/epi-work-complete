"""R6-S2 scope reconstruction v2 (PLAN_GRAPH "R6-S2 路线重构", D-1..D-5): mechanical diff check.

No mathematics is checked here. The script verifies, by exact string comparison:

  (0) v1 := `git cat-file -p HEAD:proofs/R6-S2.md` (the committed version 1 of the proof draft);
      the five moved blocks B1..B5 sit at the declared v1 line ranges (anchor checks), and the
      extra deleted lines are separator-only lines (blank or '---').
  (i) proofs/R6-S2-remarks.md: after the header (everything up to the line
      '<!-- REMARKS-BODY-BEGIN -->'), the body with the block-delimiter comment lines removed is
      exactly the concatenation of B1..B5 in v1 order; each delimited block equals its v1 range;
      the header contains the D-1 mandated paragraph verbatim (taken from PLAN_GRAPH.md), and the
      header's move table and error-location line numbers point at the right remarks lines.
 (ii) proofs/R6-S2.md (v2) equals v1 with exactly the edits in SPEC applied, and every edit falls
      into one of the five allowed classes:
        V  version line (top version line, D-3 item 5 role line, end line),
        S0 §0 re-transcription (new lines must be verbatim lines of the current PLAN_GRAPH.md and
           the replaced lines must be verbatim lines of the previous PLAN_GRAPH.md = HEAD~1),
        I3 §0.4 I3 -> "已写入陈述" and its synchronisation in the [GAP] note / "没有做到什么",
        R0 the §5.6 sentence on r_0 (text taken verbatim from PLAN_GRAPH D-3 item 4),
        P  pointer handling: pure deletion of a substring that refers to moved content,
      plus D (deletion of moved blocks and adjacent separator-only lines).
Output goes to scope_v2_diff_check.out next to this script.
"""
import difflib
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
OUT = os.path.splitext(os.path.abspath(__file__))[0] + ".out"
V2_PATH = os.path.join(ROOT, "proofs", "R6-S2.md")
REM_PATH = os.path.join(ROOT, "proofs", "R6-S2-remarks.md")
PG_PATH = os.path.join(ROOT, "PLAN_GRAPH.md")


def git_blob(rev_path):
    return subprocess.run(["git", "-C", ROOT, "cat-file", "-p", rev_path], check=True,
                          capture_output=True).stdout.decode("utf-8")


def git_rev(rev):
    return subprocess.run(["git", "-C", ROOT, "rev-parse", rev], check=True,
                          capture_output=True).stdout.decode().strip()


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


# ---------------------------------------------------------------- declarations
# Moved blocks (v1 1-indexed inclusive line ranges) with anchor predicates.
BLOCKS = [
    ("B1", 211, 213, "§5.5 末尾附注（另一种读法）",
     lambda L: L[0].startswith("- **附注（不属于对陈述的证明") and L[-1].startswith("  - （⇒）：当")),
    ("B2", 330, 330, "§7.3 指向 proofs/R6-S7-mstar.md 的子条",
     lambda L: L[0].startswith("  - 另一条独立的纯组合路线") and "R6-S7-mstar.md（同为待审稿" in L[0]),
    ("B3", 334, 364, "§8 全节",
     lambda L: L[0].startswith("## 8. ") and L[-1].startswith("  - 引理 B 的极限只依赖 α")),
    ("B4", 368, 376, "§9 全节（R1、R2、R3）",
     lambda L: L[0].startswith("## 9. ") and L[-1].startswith("- **R3**")),
    ("B5", 401, 473, "修补记录（第 1 轮）（第 2 轮）（第 3 轮）",
     lambda L: L[0] == "## 修补记录（第 1 轮）" and L[-1].startswith("- **[GAP] 数**：本轮修补后仍为 0。本轮没有引入外部定理")),
]
# Separator-only lines deleted together with the blocks.
SEPARATORS = [365, 366, 367, 377, 378, 379, 398]

VERSION_LINE = "> v2（范围重构，2026-11-27，D-1..D-5）"
END_LINE = "v1 的修补记录与附注见 `proofs/R6-S2-remarks.md`"

MOVED_REF = re.compile(r"§8|§9|\bR[123]\b|附注|另一种读法")


def pg_lines():
    return read(PG_PATH).split("\n")


def pg_quote(after):
    """Text inside “...” that follows `after` on the PLAN_GRAPH line containing it."""
    for x in pg_lines():
        i = x.find(after)
        if i >= 0:
            m = re.match(r"“(.*?)”", x[i + len(after):])
            if m:
                return m.group(1)
    raise SystemExit(f"PLAN_GRAPH anchor not found: {after}")


def pg_line(prefix):
    hits = [x for x in pg_lines() if x.startswith(prefix)]
    assert len(hits) == 1, (prefix, len(hits))
    return hits[0]


def spec():
    role = pg_quote("5. 文件头的角色说明改为")
    r0_sentence = pg_quote("4. §5.6“给定数据”一行后加一句：")
    return [
        # (v1 line, op, payload, class, note)
        (3, "replace_lines", [VERSION_LINE, f"> 角色：prover。{role}。"], "V",
         "文首版本行 + D-3 第 5 项角色说明"),
        (16, "replace_line", pg_line("- **块 Hurwitz 数**："), "S0", "§0.1 块 Hurwitz 数条目（D-2 I3）"),
        (19, "delete_sub", " 与 §9 R2", "P", "§0.1 prover 注"),
        (23, "replace_sub", ("即 2026-11-27 R6 旁支 Step 4 按审计 M2 加入规范标签定义后的版本",
                             "即 2026-11-27 strategist 路线重构 D-2（n3、I3 两处精确化）后的版本"),
         "S0", "§0.2 小标题中的版本说明"),
        (29, "replace_line", pg_line("  - (d)（实现）对任意序列"), "S0", "§0.2 S1(d)（D-2 n3）"),
        (36, "delete_sub", "；见本文 §9 备注 R1 的手算核对", "P", "§0.3 校准子条"),
        (40, "replace_sub", ("(I1) 已不再是解释性约定，只作说明；(I2)(I3) 仍是",
                             "(I1)(I3) 已不再是解释性约定，只作说明；(I2) 仍是"), "I3", "§0.4 引言"),
        (42, "delete_sub", "§5.5 末尾的“另一种读法”只是附注，不属于对陈述的证明。", "P",
         "§0.4 I1 末句（指向 B1；D-3 未列，按“凡指向”处理）"),
        (44, "replace_line",
         "- **(I3) 大指标的位置：已写入陈述（PLAN_GRAPH 2026-11-27 strategist 路线重构 D-2）。** "
         "现行 S.1 的块 Hurwitz 数条目（§0.1）直接按位置定义 $n_k:=N+(k-1)(\\ell+1)$，"
         "并写明 $N\\ge0$、$a_0\\in\\mathbb Z$、$a_1,\\dots,a_N\\in\\mathbb Z_{\\ge1}$，"
         "因此这里不再需要解释性约定。", "I3", "§0.4 I3 改为已写入陈述"),
        (53, "delete_sub", "，只在 §9 R1 中作为校准对照提及", "P", "§1 第 1 处"),
        (56, "delete_line", None, "P", "§1 第 2 处（整条只是指向 §9 R1）"),
        (58, "delete_sub", "§9 R3 与 ", "P", "§1 第 3 处"),
        (193, "delete_sub", "§8 (E1) 需要的", "P", "§5.4 有界性括注（指向 B3；D-3 未列）"),
        (217, "append", r0_sentence, "R0", "§5.6 给定数据（D-3 第 4 项，n3）"),
        (219, "delete_sub", "；§8 用到的两种代替写法见那里", "P", "§5.6 τ′ 子条"),
        (263, "delete_sub", "§8 的引用相应地写作 $g'_k$。", "P", "§5.6 (d4) 注末句（指向 B3；D-3 未列）"),
        (384, "replace_sub",
         ("§0.4 的 I1 已由陈述本身解决（规范标签已写入陈述，PLAN_GRAPH 2026-11-27 M2），"
          "不再是解释性约定；I2、I3 两条解释性约定不是缺口",
          "§0.4 的 I1、I3 已由陈述本身解决（规范标签已写入陈述，PLAN_GRAPH 2026-11-27 M2；"
          "大指标已按位置写入陈述，PLAN_GRAPH 2026-11-27 D-2），不再是解释性约定；"
          "I2 这一条解释性约定不是缺口"), "I3", "[GAP] 清单说明段"),
        (394, "delete_sub", "；它们只在 R1 中作为校准对照提及", "P", "没有做到什么：未形式化"),
        (396, "replace_sub", ("I2、I3 是本文为消除陈述歧义而采用的读法，尚未经 skeptic 认可（I1 已并入陈述",
                              "I2 是本文为消除陈述歧义而采用的读法，尚未经 skeptic 认可（I1、I3 已并入陈述"),
         "I3", "没有做到什么：解释性约定待裁决"),
        (400, "insert_after", [END_LINE], "V", "文末一行"),
    ]


def apply_spec(v1, sp):
    """Return v2 lines = v1 with blocks/separators deleted and SPEC edits applied."""
    deleted = set(SEPARATORS)
    for _, a, b, _, _ in BLOCKS:
        deleted.update(range(a, b + 1))
    ops = {n: (op, pay) for n, op, pay, _, _ in sp}
    assert not (deleted & set(ops)), "edit on a deleted line"
    out = []
    for n, x in enumerate(v1, start=1):
        if n in deleted:
            continue
        if n not in ops:
            out.append(x)
            continue
        op, pay = ops[n]
        if op == "replace_lines":
            out.extend(pay)
        elif op == "replace_line":
            out.append(pay)
        elif op == "delete_line":
            pass
        elif op == "delete_sub":
            assert x.count(pay) == 1, (n, pay)
            out.append(x.replace(pay, ""))
        elif op == "replace_sub":
            assert x.count(pay[0]) == 1, (n, pay[0])
            out.append(x.replace(pay[0], pay[1]))
        elif op == "append":
            out.append(x + pay)
        elif op == "insert_after":
            out.append(x)
            out.extend(pay)
        else:
            raise ValueError(op)
    return out


BEGIN_RE = re.compile(r"^<!-- BLOCK (B\d) BEGIN v1:L(\d+)-L(\d+) .* -->$")
END_RE = re.compile(r"^<!-- BLOCK (B\d) END -->$")
BODY_MARK = "<!-- REMARKS-BODY-BEGIN -->"


def main():
    log = []
    fails = []

    def p(s=""):
        log.append(s)

    def check(cond, msg):
        p(("PASS  " if cond else "FAIL  ") + msg)
        if not cond:
            fails.append(msg)

    head = git_rev("HEAD")
    v1_text = git_blob("HEAD:proofs/R6-S2.md")
    v1 = v1_text.split("\n")
    v2_text = read(V2_PATH)
    v2 = v2_text.split("\n")
    rem = read(REM_PATH).split("\n")
    pg_now = set(pg_lines())
    pg_prev = set(git_blob("HEAD~1:PLAN_GRAPH.md").split("\n"))
    p(f"HEAD = {head}; HEAD~1 = {git_rev('HEAD~1')}")
    p(f"v1 = HEAD:proofs/R6-S2.md (blob {git_rev('HEAD:proofs/R6-S2.md')}), {len(v1_text.splitlines())} lines")
    p(f"v2 = working-tree proofs/R6-S2.md, {len(v2_text.splitlines())} lines")
    p(f"remarks = proofs/R6-S2-remarks.md, {len(rem) - 1} lines")
    p()

    # ------------------------------------------------------------ (0) v1 anchors
    p("== (0) v1 block anchors and separators ==")
    for name, a, b, desc, pred in BLOCKS:
        check(pred(v1[a - 1:b]), f"{name} v1 L{a}-L{b} ({desc}) anchors match")
    check(all(v1[n - 1].strip() in ("", "---") for n in SEPARATORS),
          f"extra deleted lines {SEPARATORS} are blank or '---' only")
    p()

    # ------------------------------------------------------------ (i) remarks
    p("== (i) remarks body == concatenation of moved blocks ==")
    k = rem.index(BODY_MARK)
    header, body = rem[:k + 1], rem[k + 1:]
    if body and body[-1] == "":
        body = body[:-1]
    concat = [x for _, a, b, _, _ in BLOCKS for x in v1[a - 1:b]]
    stripped = [x for x in body if not (BEGIN_RE.match(x) or END_RE.match(x))]
    check(stripped == concat, f"body minus delimiter lines ({len(stripped)} lines) == B1..B5 concat ({len(concat)} lines)")
    # per-block check and remarks positions
    pos = {}
    i = 0
    order = []
    while i < len(body):
        m = BEGIN_RE.match(body[i])
        if not m:
            check(False, f"remarks body line {k + 2 + i} outside any block: {body[i][:40]!r}")
            i += 1
            continue
        name, a, b = m.group(1), int(m.group(2)), int(m.group(3))
        j = next(t for t in range(i + 1, len(body)) if END_RE.match(body[t]))
        check(END_RE.match(body[j]).group(1) == name, f"{name} END delimiter matches")
        decl = next(x for x in BLOCKS if x[0] == name)
        check((a, b) == (decl[1], decl[2]), f"{name} delimiter range L{a}-L{b} == declared")
        check(body[i + 1:j] == v1[a - 1:b], f"{name} remarks content == v1 L{a}-L{b} verbatim ({b - a + 1} lines)")
        first = k + 1 + (i + 1) + 1  # 1-indexed remarks line of first content line
        pos[name] = (first, first + (j - i - 1) - 1)
        order.append(name)
        i = j + 1
    check(order == [x[0] for x in BLOCKS], f"block order in remarks = {order}")
    htxt = "\n".join(header)
    d1 = pg_quote("的文件头必须写明：")
    check(d1 in htxt, "header contains the D-1 mandated paragraph verbatim (from PLAN_GRAPH)")
    check("不入审计，不得引用（D-1）" in htxt, "header states 不入审计、不得引用（D-1）")
    for row in re.finditer(r"^\| (B\d) \| v1 L(\d+)–L(\d+) \| .*? \| remarks L(\d+)–L(\d+) \|$", htxt, re.M):
        name, a, b, ra, rb = row.group(1), *map(int, row.groups()[1:])
        decl = next(x for x in BLOCKS if x[0] == name)
        check((a, b) == (decl[1], decl[2]) and (ra, rb) == pos[name],
              f"move table row {name}: v1 L{a}-L{b} -> remarks L{ra}-L{rb}")
    errs = {"n1": "会使 $y_n$ 最终改变 $u\\varepsilon_n$",
            "n2": "$y_{n_k}$ 也远离 $\\pm1/2$",
            "M4": "以 $\\tau_{\\max}=\\sup\\lvert\\tau_k\\rvert$ 表示即 $8K\\tau_{\\max}/\\min(A_k,A_{k+1})$"}
    for tag, phrase in errs.items():
        m = re.search(rf"\[{tag}\] remarks L(\d+)", htxt)
        ok = bool(m) and phrase in rem[int(m.group(1)) - 1]
        check(ok, f"header error marker [{tag}] points to the remarks line containing the flagged text")
    p()

    # ------------------------------------------------------------ (ii) v2 vs v1
    p("== (ii) v2 == v1 with only the declared edits ==")
    sp = spec()
    expected = apply_spec(v1, sp)
    check(expected == v2, "v2 equals v1 + {block deletion, declared edits} exactly")
    if expected != v2:
        for d in list(difflib.unified_diff(expected, v2, "expected", "v2", lineterm="", n=0))[:40]:
            p("    " + d[:160])
    allowed = {"V", "S0", "I3", "R0", "P"}
    check({c for *_, c, _ in sp} <= allowed, "every edit class is in {V, S0, I3, R0, P}")
    for n, op, pay, cls, note in sp:
        old = v1[n - 1]
        if cls == "P":
            if op == "delete_sub":
                ok = bool(MOVED_REF.search(pay))
                check(ok, f"[P]  v1 L{n} ({note}): deleted only {pay!r} (refers to moved content)")
            else:
                check(op == "delete_line" and bool(MOVED_REF.search(old)),
                      f"[P]  v1 L{n} ({note}): whole line deleted, it only points to moved content: {old.strip()!r}")
        elif cls == "S0":
            if op == "replace_line":
                check(pay in pg_now and old in pg_prev and old not in pg_now,
                      f"[S0] v1 L{n} ({note}): old line = previous PLAN_GRAPH, new line = current PLAN_GRAPH verbatim")
            else:
                check(op == "replace_sub" and pay[0] in old,
                      f"[S0] v1 L{n} ({note}): heading version remark {pay[0]!r} -> {pay[1]!r}")
        elif cls == "R0":
            check(op == "append" and "r_0" in pay, f"[R0] v1 L{n} ({note}): appended {pay!r} (verbatim D-3 item 4)")
        elif cls == "I3":
            desc = pay if op == "replace_line" else f"{pay[0]!r} -> {pay[1]!r}"
            check(True, f"[I3] v1 L{n} ({note}): {str(desc)[:150]}")
        elif cls == "V":
            check(True, f"[V]  v1 L{n} ({note}): {pay}")
    # §0 statement lines of v2 are verbatim current PLAN_GRAPH lines
    s = v2.index("### 0.1 记号（S.1，逐字，共 7 条，供定位；本文件不改动任何一条）")
    e = next(i for i, x in enumerate(v2) if x.startswith("### 0.4 "))
    stmt = [x for x in v2[s + 1:e] if x.startswith("- **") or re.match(r"^  - \([a-d]\)", x)
            or x.startswith("- $")]
    miss = [x[:50] for x in stmt if x not in pg_now]
    check(not miss and len(stmt) == 13, f"v2 §0.1–§0.3: all {len(stmt)} statement lines are verbatim current PLAN_GRAPH lines {miss}")
    check("I2、I3" not in v2_text and "(I2)(I3)" not in v2_text, "v2 no longer lists I3 as pending")
    check(v2[2] == VERSION_LINE and END_LINE in v2[-3:], "version line at top, end line at bottom")
    gaps = re.findall(r"\[GAP-\d+\]", v2_text)
    gi = v2.index("## [GAP] 清单")
    check(not gaps and v2[gi + 2] == "无。", f"[GAP] list in v2: '无。', [GAP-k] occurrences = {len(gaps)}")
    p()

    # ------------------------------------------------------------ informational
    p("== residual mentions in v2 (informational, not failures) ==")
    for i, x in enumerate(v2, start=1):
        hits = sorted(set(re.findall(r"§8|§9|\bR[123]\b|附注|修补|remarks", x)))
        if hits:
            p(f"  v2 L{i}: {hits}  {x.strip()[:70]}")
    p()
    sm = difflib.SequenceMatcher(a=v1, b=v2, autojunk=False)
    nd = sum(i2 - i1 for t, i1, i2, _, _ in sm.get_opcodes() if t in ("delete", "replace"))
    ni = sum(j2 - j1 for t, _, _, j1, j2 in sm.get_opcodes() if t in ("insert", "replace"))
    p(f"difflib summary: v1 lines removed/replaced = {nd}, v2 lines inserted/replacing = {ni}")
    p()
    p("ALL CHECKS PASSED" if not fails else f"{len(fails)} CHECK(S) FAILED")
    with open(OUT, "w", encoding="utf-8") as f:
        f.write("\n".join(log) + "\n")
    print("\n".join(log))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
