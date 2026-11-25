# -*- coding: utf-8 -*-
"""
Numeric cross-check of numerical constants quoted in
paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex (2026-11-24 state).
Read-only with respect to the repo: this script only computes; it writes nothing
into paper2_spectral_gap_dimension/.
Run:  python paper2_numeric_check_20261124.py
"""
from decimal import Decimal, getcontext
import sys

getcontext().prec = 60

def D(x):
    return Decimal(x)

# ---------- (a) psi_Fib = sum_{k>=1} 1/F_k ----------
def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

def reciprocal_fib_sum(kmax=200):
    s = Decimal(0)
    for k in range(1, kmax + 1):
        s += Decimal(1) / Decimal(fib(k))
    return s

psi = reciprocal_fib_sum()

def round_str(d, nd):
    q = Decimal(10) ** (-nd)
    return str(d.quantize(q))
print("[a] psi_Fib = sum_{k>=1} 1/F_k (kmax=200):")
print("    computed (12dp) =", round_str(psi, 12))
print("    paper    = 3.359885666243  (tab:residues-asymptotic, r=1 row)")
print("    abstract = 3.3598856662    (eq. for C_1=psi_Fib, 10dp)")
print("    match_to_12dp =", round_str(psi, 12) == "3.359885666243")

# ---------- (b) C_r = sum 1/q_n(r), metallic continuants q_0=1,q_1=r,q_{n+2}=r q_{n+1}+q_n ----------
def metallic_series(r, kmax=200):
    q = []
    q0, q1 = 1, r
    q.extend([q0, q1])
    for _ in range(kmax):
        q.append(r * q[-1] + q[-2])
    s = Decimal(0)
    for qn in q:
        s += Decimal(1) / Decimal(qn)
    return s

paper_C = {1: "3.359885666243", 2: "1.842203049828", 3: "1.476794726319",
           4: "1.327004277866", 5: "1.247635731173"}
def round_str(d, nd):
    q = Decimal(10) ** (-nd)
    return str(d.quantize(q))

print("\n[b] C_r = sum_{n>=0} 1/q_n(r) vs tab:residues-asymptotic (paper value = 12dp rounding):")
for r in range(1, 6):
    c = metallic_series(r)
    ok = round_str(c, 12) == paper_C[r]
    print(f"    r={r}: computed={round_str(c,12)}  paper={paper_C[r]}  match_12dp={ok}")

# ---------- (c) two-term asymptotic s_2term(1000, r) = 1/2 + C_r/(2m) - C_r^2 log m /(2 m^2), m=1000 ----------
def ln(x, terms=200):
    # natural log via AtanSeries-free approach: use decimal ln
    return Decimal(x).ln()

m = 1000
print("\n[c] s_2term(1000,r)=1/2+C_r/(2m)-C_r^2*log(m)/(2m^2) vs tab column 's_2term(1000,r)':")
paper_s2 = {1: "0.5016409526", 2: "0.5009093801", 3: "0.5007308647",
            4: "0.5006574201", 5: "0.5006184416"}
logm = ln(m)
for r in range(1, 6):
    C = metallic_series(r)
    s2 = D(1)/D(2) + C/(2*m) - (C*C*logm)/(2*m*m)
    ok = round_str(s2, 10) == paper_s2[r]
    print(f"    r={r}: computed={round_str(s2,10)}  paper={paper_s2[r]}  match_10dp={ok}")

# ---------- (d) Regime II: A_j=2^{2^j}, Q_0=Q_1=1, Q_{j+1}=A_j Q_j + Q_{j-1}; limit Q_j/A_j ----------
print("\n[d] Regime II (cor:growing-rec-three-regimes): A_j=2^{2^j}, Q_0=Q_1=1.")
print("    Q_{j+1}=A_j*Q_j+Q_{j-1} (so Q_2=A_1*Q_1+Q_0=5); ratio Q_j/A_j and inverse:")
Q = [1, 1]                  # Q[0], Q[1]
for j in range(1, 12):
    A_j = 2 ** (2 ** j)
    Q.append(A_j * Q[j] + Q[j - 1])   # Q_{j+1}
for j in range(1, 11):
    A_j = 2 ** (2 ** j)
    ratio = Decimal(Q[j]) / Decimal(A_j)
    inv = Decimal(A_j) / Decimal(Q[j])
    print(f"    j={j:2d}: Q_j={len(str(Q[j]))}d  Q_j/A_j = {str(ratio)[:22]}   A_j/Q_j = {str(inv)[:14]}")
A_10 = 2 ** (2 ** 10)
lim_ratio = Decimal(Q[10]) / Decimal(A_10)   # j=10: correction term r/A_j^2 < 10^-600
print("    computed limit Q_j/A_j (j=10) =", str(lim_ratio)[:20])
print("    computed inverse A_j/Q_j  (j=10) =", str(D(1)/lim_ratio)[:20])
print("    paper: lim Q_j/A_j ~ 0.316420  (cor:growing-rec-three-regimes statement)")
print("    paper: (lim Q_j/A_j)^{-1} ~ 3.15973  (sec:num, double-exponential tau=2 check)")
print("    1/0.316420 = " + round_str(D(1)/Decimal('0.316420'), 10))
print("    1/3.15973  = " + round_str(D(1)/Decimal('3.15973'), 12))

# ---------- (e) decimal expansions of the certified fraction bounds (tab:residues-general) ----------
print("\n[e] tab:residues-general fraction decimal expansions:")
tab = [("2","1","105/128","0.820312","421/512","0.822266"),
       ("2","2","23/32","0.718750","369/512","0.720703"),
       ("3","1","95/128","0.742188","381/512","0.744141"),
       ("3","3","41/64","0.640625","329/512","0.642578"),
       ("4","1","357/512","0.697266","179/256","0.699219"),
       ("4","4","309/512","0.603516","155/256","0.605469"),
       ("5","1","171/256","0.667969","343/512","0.669922"),
       ("5","5","149/256","0.582031","299/512","0.583984"),
       ("6","1","331/512","0.646484","83/128","0.648438"),
       ("6","6","291/512","0.568359","73/128","0.570312")]
def frac(s):
    a, b = s.split("/")
    return Decimal(int(a)) / Decimal(int(b))
all_ok = True
for row in tab:
    lo, lo_dec, hi, hi_dec = frac(row[2]), row[3], frac(row[4]), row[5]
    ok1 = round_str(lo, 6) == lo_dec
    ok2 = round_str(hi, 6) == hi_dec
    all_ok = all_ok and ok1 and ok2
    print(f"    m={row[0]} r={row[1]}: lower {row[2]}={round_str(lo,6)} vs {lo_dec} ({'ok' if ok1 else 'MISMATCH'}); "
          f"upper {row[4]}={round_str(hi,6)} vs {hi_dec} ({'ok' if ok2 else 'MISMATCH'})")
print("    all decimal roundings in table consistent:", all_ok)

# ---------- (f) width checks: upper-lower = 1/512 and separation upper(F_{m,m}) < lower(F_{m,1}) ----------
print("\n[f] width=1/512 and strict separation per modulus:")
for mrow in [("2",0,1),("3",2,3),("4",4,5),("5",6,7),("8" if False else "6",8,9)]:
    pass
rows = tab
for mm in ["2","3","4","5","6"]:
    r1 = next(x for x in rows if x[0]==mm and x[1]=="1")
    rm = next(x for x in rows if x[0]==mm and x[1]==mm)
    w1 = frac(r1[4]) - frac(r1[2]); wm = frac(rm[4]) - frac(rm[2])
    sep = frac(rm[4]) < frac(r1[2])
    print(f"    m={mm}: width(r=1)={str(w1)[:12]} width(r=m)={str(wm)[:12]} both=1/512={w1==D(1)/512 and wm==D(1)/512}; upper(F_mm)<lower(F_m1)={sep}")
print("done.")
