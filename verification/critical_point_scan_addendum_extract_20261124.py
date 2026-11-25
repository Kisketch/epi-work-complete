# -*- coding: utf-8 -*-
"""E3 增补记录的表格提取器（只读；不改任何文件）。
从 v2 诊断 / v2 标度复核输出摘录 ratio obs/model 与 alpha_loc（注意：诊断行 m 的 alpha_loc = log2(delta(m)/delta(2m))，
即刻画倍增段 m→2m），从 JSONL 取 n=16/24 原始串算差值与派生局部指数。
用法（在仓库根目录）：  .venv\\Scripts\\python.exe verification\\critical_point_scan_addendum_extract_20261124.py
输出：打印表 A、表 B 与若干数据事实，供 critical_point_scan_addendum_20261124.md 照录。
"""
import json
import math
import re
from collections import Counter

from mpmath import mp, mpf

mp.dps = 30
V = "verification"
DIAG = open(V + r"\critical_point_scan_20261124_diagnostics_v2.md", encoding="utf-8-sig").read()
SCAL = open(V + r"\critical_scaling_check_20261124_output_v2.md", encoding="utf-8-sig").read()
JSONL = V + r"\critical_point_scan_20261124.jsonl"


def parse(text, head_re):
    out, cur, heads = {}, None, {}
    for ln in text.splitlines():
        h = re.match(head_re, ln)
        if h:
            cur = (h.group(1), h.group(2))
            out[cur] = []
            heads[cur] = ln
        elif cur and re.match(r"\| \d+ \|", ln):
            out[cur].append([c.strip() for c in ln.strip().strip("|").split("|")])
    return out, heads


D, DH = parse(DIAG, r"^## S=(\[[^\]]*\])  B=(\[[^\]]*\])")
S, SH = parse(SCAL, r"^### S=(\[[^\]]*\]) B=(\[[^\]]*\])")
kappa = {}
for ln in SCAL.splitlines():
    m = re.match(r"\| (\[[^\]]*\]) \| [\d.]+ \| (-?[\d.]+) \| [\d.]+ \| [\d.]+ \| ([\d.]+) \|", ln)
    if m:
        kappa[m.group(1)] = m.group(3)

recs = [json.loads(l) for l in open(JSONL, encoding="utf-8") if l.strip()]
scan = {(tuple(r["S"]), tuple(r["B"]), r["m"], r["n"]): r for r in recs if r.get("stage") == "scan"}


def dim_str(Sx, Bx, m, n):
    return scan[(tuple(eval(Sx)), tuple(eval(Bx)), m, n)]["dim"]


def delta(Sx, Bx, m):
    r = scan[(tuple(eval(Sx)), tuple(eval(Bx)), m, 16)]
    return mpf(r["dim"]) - mpf(r["center"])


print("## 表 A：j=13–16（B=∅ 与 B={1}）：ratio obs/model（摘自 v2 标度复核）与 alpha_loc（摘自 v2 诊断）")
print()
print("诊断行值约定：α_loc@x 列取 m=x 行的值 = log₂(Δ(x)/Δ(2x))，刻画倍增段 x→2x；j=13–16 无 m=32768 点，故无 x=16384 的行值。")
print()
print("| j | B | s0−1/2 | κ(S) | m*=dκ/η² | Δ(16384) | ratio@1024 | ratio@4096 | ratio@16384 | α_loc@1024(→2048) | α_loc@4096(→8192) | α_loc@8192(→16384) | |n16−n24|@4096 |")
print("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for j in (13, 14, 15, 16):
    Sx = "[3, 4, 5, %d]" % j if False else "[3, 4, 5, 6, %d]" % j
    for Bx in ("[]", "[1]"):
        hd = re.search(r"\(s0-1/2=([+-]?[\d.]+)\)", DH[(Sx, Bx)]).group(1)
        hs = re.search(r"crossover m\*~([\d.e+]+)", SH[(Sx, Bx)]).group(1)
        drow = {r[0]: r for r in D[(Sx, Bx)]}
        srow = {r[0]: r for r in S[(Sx, Bx)]}
        d16, d24 = dim_str(Sx, Bx, 4096, 16), dim_str(Sx, Bx, 4096, 24)
        print("| %d | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s（串%s） |" % (
            j, "∅" if Bx == "[]" else "{1}", hd, kappa[Sx], hs,
            drow["16384"][2], srow["1024"][3], srow["4096"][3], srow["16384"][3],
            drow["1024"][3] or "—", drow["4096"][3] or "—", drow["8192"][3] or "—",
            mp.nstr(abs(mpf(d16) - mpf(d24)), 3), "同" if d16 == d24 else "异"))

print()
print("## 表 B：m=32768、65536（最近临界两组，B=∅）")
print()
print("α_loc 行值同上约定（行 m 的值覆盖段 m→2m）；「α rel.16384」= log(Δ(16384)/Δ(m))/log(m/16384)。")
print()
print("| S | m | dim(n=16) | Δ=dim−center | α_loc 行值(段 m→2m) | α rel.16384 | ratio obs/model | window |")
print("|---|---:|---:|---:|---:|---:|---:|:---:|")
for Sx in ("[3, 4, 5, 6, 9]", "[3, 4, 5, 6, 10]"):
    d16384 = delta(Sx, "[]", 16384)
    drow = {r[0]: r for r in D[(Sx, "[]")]}
    srow = {r[0]: r for r in S[(Sx, "[]")]}
    print("| %s | 16384 | %s | %s | %s | —（基准） | %s | %s |" % (
        Sx, drow["16384"][1], drow["16384"][2], drow["16384"][3] or "—", srow["16384"][3], srow["16384"][4]))
    for m in (32768, 65536):
        d = delta(Sx, "[]", m)
        rel = math.log(d16384 / d) / math.log(m / 16384)
        print("| %s | %d | %s | %s | %s | %s | %s | %s |" % (
            Sx, m, drow[str(m)][1], drow[str(m)][2],
            drow[str(m)][3] if drow[str(m)][3] else "—（无 m=131072 点）",
            mp.nstr(rel, 3), srow[str(m)][3], srow[str(m)][4]))

print()
print("## 数据事实（代码输出）")
print()
print("### (a) 沿族 j=7–16、B=∅：Δ(16384) 与 ratio@16384（连续性检查）")
print("| j | s0−1/2 | Δ(16384) | ratio@16384 |")
print("|---|---:|---:|---:|")
for j in range(7, 17):
    Sx = "[3, 4, 5, 6, %d]" % j
    hd = re.search(r"\(s0-1/2=([+-]?[\d.]+)\)", DH[(Sx, "[]")]).group(1)
    drow = {r[0]: r for r in D[(Sx, "[]")]}
    srow = {r[0]: r for r in S[(Sx, "[]")]}
    print("| %d | %s | %s | %s |" % (j, hd, drow["16384"][2], srow["16384"][3]))
print()
print("### (b) 深点派生指数（mpmath，自 JSONL 原始串）与 v2 诊断行值互核")
for Sx in ("[3, 4, 5, 6, 9]", "[3, 4, 5, 6, 10]"):
    d1, d2, d3 = (delta(Sx, "[]", m) for m in (16384, 32768, 65536))
    print("%s: log2(Δ16384/Δ32768)=%s（诊断 16384 行值 0.584/0.524 对应段），log2(Δ32768/Δ65536)=%s（诊断 32768 行值 0.627/0.545），"
          "log2(Δ16384/Δ65536)/2=%s" % (Sx, mp.nstr(mp.log(d1 / d2, 2), 5), mp.nstr(mp.log(d2 / d3, 2), 5), mp.nstr(mp.log(d1 / d3, 2) / 2, 5)))
print()
print("### (c) n=16 与 n=24 校验点的 30 位串比较（本次新增 8 个 m=4096 校验点）")
for j in (13, 14, 15, 16):
    for Bx in ("[]", "[1]"):
        Sx = "[3, 4, 5, 6, %d]" % j
        d16, d24 = dim_str(Sx, Bx, 4096, 16), dim_str(Sx, Bx, 4096, 24)
        print("S=%s B=%s m=4096: 串相同=%s |n16−n24|=%s" % (Sx, Bx, d16 == d24, mp.nstr(abs(mpf(d16) - mpf(d24)), 3)))
same = 0
tot = 0
for (S, B, m, n), r in scan.items():
    if n == 24 and (S, B, m, 16) in scan:
        tot += 1
        if scan[(S, B, m, 16)]["dim"] == r["dim"]:
            same += 1
print("全 JSONL n=24 校验点共 %d 个，其中与 n=16 的 30 位串完全相同 %d 个" % (tot, same))
print()
print("### (d) 计数与既有遗留")
sc = [r for r in recs if r.get("stage") == "scan"]
new = [r for r in sc if (len(r["S"]) == 5 and r["S"][:4] == [3, 4, 5, 6] and r["S"][4] in (13, 14, 15, 16)) or r["m"] >= 32768]
print("JSONL 总记录 %d；scan 记录 %d；本次新增 scan 记录 %d（键唯一：%s）；新增中 n=16：%d，n=24：%d" % (
    len(recs), len(sc), len(new), len(set(r["key"] for r in new)) == len(new),
    sum(1 for r in new if r["n"] == 16), sum(1 for r in new if r["n"] == 24)))
print("新增 scan 记录耗时合计 %.0f s（各 worker 进程计时之和，非墙钟）" % sum(r["secs"] for r in new))
cnt = Counter(r["key"] for r in recs)
for k, c in cnt.items():
    if c > 1:
        vals = [r.get("s0", r.get("dim")) for r in recs if r["key"] == k]
        print("key=%s 出现 %d 次，数值一致：%s（v1 遗留，本次未触碰）" % (k, c, len(set(vals)) == 1))
print("s0 记录 %d 条，去重后 %d 个 key" % (sum(1 for r in recs if r.get("stage") == "s0"), len({r["key"] for r in recs if r.get("stage") == "s0"})))
