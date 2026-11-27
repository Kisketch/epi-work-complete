#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
R6 Step 2 (skeptic, mode_falsify): falsification test for node R6-N4
("e-scale universality" of pi), as specified in PLAN_GRAPH.md, section "当前主攻".

Category 4 (finite computation). Nothing here proves anything about pi beyond
the finite range j in (1000,2000], n in (2000,4000], B <= 30.

Definitions (PLAN_GRAPH.md, R6-N4; checked against Paper 1 thm:adaptive-strip,
thm:factorial-quantization):
  Q_0=Q_1=1, P_0=1, P_1=3, X_{j+1}=(4j+2)X_j+X_{j-1}.
  E_j(B;x) = j*||B Q_j x||
  H_j(B;x) = 1 iff some regular-CF convergent denominator of x lies in
             S(j,B) = [2 B Q_j, j Q_j / B]          (only for 2B^2 < 1000)
  Phi_n(x) = floor((n+1) * frac(n! * (-x)))
  S1_B = #{j in W : E_j < 1/4},  S2_B = #{j in W : H_j = 0},
  S3   = #{n in W' : Phi_n = 1},  S4_B = KS distance of {frac(B Q_j x): j in W}
         from Uniform[0,1).
  W=(1000,2000], W'=(2000,4000].

Implementation notes
  * Every object x is represented by an integer X and a certified bracket
    x in [(X-lo_err)/2^P, (X+hi_err)/2^P].  All fractional parts are computed
    exactly in integer arithmetic mod 2^P; every threshold comparison is
    checked against a rigorous worst-case error bound ("margin check").
  * Continued fractions are computed from BOTH bracket endpoints; only the
    common prefix (which is a prefix of the CF of x, because a CF cylinder is
    an interval) is used.  We require the last certified convergent
    denominator to exceed T_max = J*Q_J (the largest strip end), otherwise the
    run aborts.  This is where the spec's precision rule is insufficient --
    see PRECISION FIX below.
  * KS statistic is computed exactly on the 60-bit truncations of the points;
    D is stored as the exact integer D_num = n*2^60*D.
  * Reference set: 400 reals 3 + 0.b1 b2 b3 ... (binary), bits drawn from
    SHAKE-256(SEED || index); the stream is prefix-consistent, so the base run
    and the 1.5x run use the SAME reals (the 1.5x run just sees more bits).

PRECISION FIX (skeptic): the spec's working precision
    max(log10(30 Q_{J+1}), log10((N+1)!)) + 200
does not suffice for S2, which needs the CF of x up to denominators
~ J*Q_J ~ 10^{6948}, i.e. an enclosure of width ~ (J Q_J)^{-2}.  We use
    dps = max(log10(30 Q_{J+1}), log10((N+1)!), 2*log10(J*Q_J)) + 200
and the diagnostic section shows the spec value fails the certification.

GATE FIX (skeptic): sqrt2 has q_{k+1}/q_k = 2 + q_{k-1}/q_k < 2.5, and the strip
ratio is j/(2B^2) >= 1001/(2B^2) >= 2.5 for B <= 14, so S2_B(sqrt2) = 0 is forced
for B <= 14 and gate v2 as written must fail regardless of pi.  The script
reports the spec-literal verdict and the corrected one (v2* = v2 without sqrt2;
v2** = sqrt2 replaced by 2^(1/3)).  The output (.out) is rewritten on each run.
"""
import sys, time, math, hashlib, bisect, json
from multiprocessing import Pool
import mpmath
from mpmath import mp

# ---------------- parameters (from PLAN_GRAPH.md) ----------------
J = 2000
N = 4000
BMAX = 30
W = list(range(1001, 2001))          # (1000, 2000]
WP = list(range(2001, 4001))         # (2000, 4000]
BS = list(range(1, BMAX + 1))
BS2 = [B for B in BS if 2 * B * B < 1000]
NREF = 400
SEED = b"R6-N4/skeptic/2026-11-26/seed=0x5EED2026"
GUARD = 200
KSBITS = 60

# ---------------- exact recurrences ----------------
Q = [1, 1]
Pn = [1, 3]
for j in range(1, J + 2):
    Q.append((4 * j + 2) * Q[j] + Q[j - 1])
    Pn.append((4 * j + 2) * Pn[j] + Pn[j - 1])
TMAX = J * Q[J]          # max_{j<=J, B>=1} j Q_j / B


def _log10_int(n):
    # exact enough: use bit length + leading 64 bits
    b = n.bit_length()
    if b <= 64:
        return math.log10(n)
    lead = n >> (b - 64)
    return math.log10(lead) + (b - 64) * math.log10(2)


d1 = _log10_int(30 * Q[J + 1])
fact_N1 = math.factorial(N + 1)
d2 = _log10_int(fact_N1)
d3 = 2 * _log10_int(TMAX)
DPS_SPEC = math.ceil(max(d1, d2)) + GUARD
DPS_FIX = math.ceil(max(d1, d2, d3)) + GUARD

# ---------------- globals set per run ----------------
G = {}


def setup_run(dps):
    P = math.ceil(dps * math.log2(10))
    G['P'] = P
    G['M'] = 1 << P
    G['MASK'] = (1 << P) - 1
    G['f2001'] = math.factorial(WP[0])


def mp_to_bracket(v, P):
    """v: mpf computed at prec >= P+90. Returns X, lo_err, hi_err (units 2^-P)."""
    X = int(mpmath.floor(mpmath.ldexp(v, P)))
    return X, 1, 2


def random_bracket(i, P):
    nbytes = (P + 7) // 8
    h = hashlib.shake_256(SEED + b"|" + str(i).encode()).digest(nbytes)
    bits = int.from_bytes(h, 'big') >> (8 * nbytes - P)
    X = (3 << P) + bits
    return X, 0, 1     # x in [X, X+1]/2^P


def cf_common_prefix_denoms(a1, a2, b, stop):
    """Common CF prefix of a1/b and a2/b (a1<a2). Returns list of convergent
    denominators q_0..q_K that are certified for every real in [a1/b, a2/b],
    stopping once q_K > stop. Returns (qs, reached)."""
    qs = []
    qm2, qm1 = 0, 1   # q_{-2}? use standard: q_{-1}=0, q_0=1
    # a_0
    c1, r1 = divmod(a1, b)
    c2, r2 = divmod(a2, b)
    if c1 != c2:
        return qs, False
    qprev, q = 0, 1
    qs.append(q)
    n1, d1_ = b, r1
    n2, d2_ = b, r2
    while True:
        if d1_ == 0 or d2_ == 0:
            return qs, q > stop
        c1, r1 = divmod(n1, d1_)
        c2, r2 = divmod(n2, d2_)
        if c1 != c2:
            return qs, q > stop
        qprev, q = q, c1 * q + qprev
        qs.append(q)
        if q > stop:
            return qs, True
        n1, d1_ = d1_, r1
        n2, d2_ = d2_, r2


def stats_for(X, lo_err, hi_err):
    P, M, MASK = G['P'], G['M'], G['MASK']
    eb = max(lo_err, hi_err)
    out = {}
    amb = 0
    # frac(Q_j x) * 2^P
    Fq = {j: (Q[j] * X) & MASK for j in W}
    # S1 and S4
    for B in BS:
        s1 = 0
        U = []
        for j in W:
            F = (B * Fq[j]) & MASK
            d = F if F <= M - F else M - F
            lhs = 4 * j * d
            err = 4 * j * B * Q[j] * eb
            if abs(lhs - M) <= err:
                amb += 1
            if lhs < M:
                s1 += 1
            U.append(F >> (P - KSBITS))
        out['S1_%d' % B] = s1
        U.sort()
        n = len(U)
        one = 1 << KSBITS
        dnum = 0
        for i, u in enumerate(U, start=1):
            a = i * one - n * u
            c = n * u - (i - 1) * one
            if a > dnum:
                dnum = a
            if c > dnum:
                dnum = c
        out['S4num_%d' % B] = dnum      # D = dnum / (n * 2^60)
    # S3 : Phi_n(x) = floor((n+1) frac(n!(-x)))
    T = (G['f2001'] * (-X)) & MASK
    errlog = _log10_int(G['f2001']) + math.log10(eb + 1)
    s3 = 0
    digits = []
    for n in WP:
        V = (n + 1) * T
        phi = V >> P
        T = V & MASK
        errlog += math.log10(n + 1)
        r = T if T <= M - T else M - T
        if r == 0 or _log10_int(r) - P * math.log10(2) <= errlog - P * math.log10(2) + 1:
            amb += 1
        if phi == 1:
            s3 += 1
        digits.append(phi)
    out['S3'] = s3
    out['_phi_first'] = digits[:5]
    out['_phi_last'] = digits[-5:]
    # blind-spot diagnostic: digits in {0, n} (extreme factorial digits)
    out['_phi_extreme'] = sum(1 for n, d in zip(WP, digits) if d == 0 or d == n)
    # S2 : convergent denominators of x up to > TMAX
    qs, reached = cf_common_prefix_denoms(X - lo_err, X + hi_err, M, TMAX)
    out['_cf_reached'] = reached
    out['_cf_len'] = len(qs)
    out['_cf_maxq_log10'] = _log10_int(qs[-1]) if qs else 0.0
    # max ratio of consecutive certified convergent denominators with q >= 2 Q_1001
    lo0 = 2 * Q[W[0]]
    big = [q for q in qs if q >= lo0 // 64]
    out['_cf_maxratio_num'] = max((big[i + 1] * 1000) // big[i] for i in range(len(big) - 1)) if len(big) > 1 else 0
    if reached:
        for B in BS2:
            s2 = 0
            for j in W:
                lo = 2 * B * Q[j]
                k = bisect.bisect_left(qs, lo)
                hit = k < len(qs) and B * qs[k] <= j * Q[j]
                if not hit:
                    s2 += 1
            out['S2_%d' % B] = s2
    out['_amb'] = amb
    return out


def worker(task):
    kind, payload = task
    P = G['P']
    if kind == 'rand':
        X, le, he = random_bracket(payload, P)
        name = 'R%03d' % payload
    else:
        name, X, le, he = payload
    t = time.time()
    st = stats_for(X, le, he)
    st['_time'] = time.time() - t
    return name, st


def named_objects(dps):
    P = G['P']
    mp.prec = P + 128
    e = mp.e
    objs = [
        ('pi', +mp.pi),
        ('exp(sqrt2)', mp.exp(mp.sqrt(2))),
        ('cos1', mp.cos(1)),
        ('sqrt2', mp.sqrt(2)),
        ('cbrt2', mp.cbrt(2)),
        ('6-e', mpmath.mpf(6) - e),
        ('11/2-e', mpmath.mpf(11) / 2 - e),
        ('17/3-e', mpmath.mpf(17) / 3 - e),
    ]
    res = []
    for name, v in objs:
        X, le, he = mp_to_bracket(v, P)
        res.append((name, X, le, he))
    # exact delta premise: |Q_j e - P_j| < 1/(2 j Q_j) for j in W
    Xe, _, _ = mp_to_bracket(e, P)
    ok = True
    worst = -1e18
    for j in W:
        # Q_j e - P_j = (Q_j Xe - P_j 2^P)/2^P + err, |err| <= 2 Q_j / 2^P
        num = Q[j] * Xe - Pn[j] * G['M']
        if 2 * j * Q[j] * (abs(num) + 2 * Q[j]) >= G['M']:
            ok = False
        worst = max(worst, _log10_int(2 * j * Q[j] * abs(num)) - P * math.log10(2))
    return res, ok, worst


def run(dps, nproc=6):
    setup_run(dps)
    t0 = time.time()
    named, delta_ok, delta_worst = named_objects(dps)
    tasks = [('named', o) for o in named] + [('rand', i) for i in range(NREF)]
    with Pool(nproc) as pool:
        results = dict(pool.map(worker, tasks, chunksize=4))
    return results, delta_ok, delta_worst, time.time() - t0


def stat_keys():
    ks = ['S1_%d' % B for B in BS] + ['S2_%d' % B for B in BS2] + ['S3'] + ['S4num_%d' % B for B in BS]
    return ks


def main():
    log = []
    def p(*a):
        s = ' '.join(str(x) for x in a)
        print(s, flush=True)
        log.append(s)

    p('# R6-N4 falsification test (skeptic, R6 Step 2). Category 4: finite computation.')
    p('# python', sys.version.split()[0], 'mpmath', mpmath.__version__, 'backend', mpmath.libmp.BACKEND)
    p('# J=%d N=%d BMAX=%d |W|=%d |W\'|=%d NREF=%d' % (J, N, BMAX, len(W), len(WP), NREF))
    p('# SEED =', SEED.decode())
    p('# S2 B-list (2B^2<1000):', BS2)
    p('# log10(30 Q_{J+1}) = %.3f ; log10((N+1)!) = %.3f ; 2 log10(J Q_J) = %.3f' % (d1, d2, d3))
    p('# DPS_SPEC (spec rule) = %d ; DPS_FIX (skeptic rule incl. S2 CF need) = %d' % (DPS_SPEC, DPS_FIX))

    # ---- diagnostic: spec precision insufficient for S2 ----
    setup_run(DPS_SPEC)
    named, _, _ = named_objects(DPS_SPEC)
    p('## Diagnostic at DPS_SPEC: certified CF prefix vs T_max = J Q_J (log10 T_max = %.3f)' % _log10_int(TMAX))
    for name, X, le, he in named[:2]:
        qs, reached = cf_common_prefix_denoms(X - le, X + he, G['M'], TMAX)
        p('  %-12s certified convergents: %d, largest certified q has log10 = %.1f, reaches T_max: %s'
          % (name, len(qs), _log10_int(qs[-1]), reached))
    for i in range(3):
        X, le, he = random_bracket(i, G['P'])
        qs, reached = cf_common_prefix_denoms(X - le, X + he, G['M'], TMAX)
        p('  R%03d         certified convergents: %d, largest certified q has log10 = %.1f, reaches T_max: %s'
          % (i, len(qs), _log10_int(qs[-1]), reached))

    # ---- main run and 1.5x run ----
    dps_a = DPS_FIX
    dps_b = math.ceil(1.5 * DPS_FIX)
    resA, dokA, dwA, tA = run(dps_a)
    p('## Run A: dps=%d (P=%d bits), time %.1fs' % (dps_a, G['P'], tA))
    p('   premise |Q_j e-P_j| < 1/(2jQ_j) for all j in W (rigorous): %s ; max log10(2jQ_j|delta_j|) = %.4f' % (dokA, dwA))
    resB, dokB, dwB, tB = run(dps_b)
    p('## Run B: dps=%d (P=%d bits), time %.1fs' % (dps_b, G['P'], tB))
    p('   premise check: %s' % dokB)

    keys = stat_keys()
    # validity of runs
    bad_cf = [n for n, s in resA.items() if not s['_cf_reached']] + [n for n, s in resB.items() if not s['_cf_reached']]
    amb = sum(s['_amb'] for s in resA.values()) + sum(s['_amb'] for s in resB.values())
    mism = []
    for name in resA:
        for k in keys:
            if resA[name].get(k) != resB[name].get(k):
                mism.append((name, k, resA[name].get(k), resB[name].get(k)))
    p('## Consistency: CF certification failures: %d ; margin ambiguities: %d ; A/B mismatches: %d' % (len(bad_cf), amb, len(mism)))
    for m in mism[:20]:
        p('   MISMATCH', m)
    INVALID_PREC = bool(bad_cf or amb or mism)

    R = resA
    refnames = ['R%03d' % i for i in range(NREF)]
    named_names = ['pi', 'exp(sqrt2)', 'cos1', 'sqrt2', 'cbrt2', '6-e', '11/2-e', '17/3-e']

    # dump full table
    with open(__file__.replace('.py', '_stats.tsv'), 'w') as fh:
        fh.write('name\t' + '\t'.join(keys) + '\n')
        for name in named_names + refnames:
            fh.write(name + '\t' + '\t'.join(str(R[name][k]) for k in keys) + '\n')

    def rng(k, exclude=None):
        vals = [R[y][k] for y in refnames if y != exclude]
        return min(vals), max(vals)

    def O(y):
        cnt = 0
        out = []
        for k in keys:
            lo, hi = rng(k, exclude=y if y in refnames else None)
            v = R[y][k]
            if v < lo or v > hi:
                cnt += 1
                out.append(k)
        return cnt, out

    # reference summary
    p('## Reference set summary (Run A): stat : min / mean / max')
    nks = len(W) * (1 << KSBITS)
    for k in keys:
        vals = [R[y][k] for y in refnames]
        if k.startswith('S4num'):
            p('   %-9s %.5f / %.5f / %.5f' % ('S4_' + k[6:], min(vals) / nks, sum(vals) / len(vals) / nks, max(vals) / nks))
        else:
            p('   %-9s %d / %.3f / %d' % (k, min(vals), sum(vals) / len(vals), max(vals)))
    # R6-N1 reference bound for S2
    p('## R6-N1 reference upper bound sum_{j in W} 4B^2/j vs. reference-set mean S2_B (vs |W|=1000)')
    for B in BS2:
        bound = sum(mpmath.mpf(4 * B * B) / j for j in W)
        mean = sum(R[y]['S2_%d' % B] for y in refnames) / NREF
        p('   B=%2d bound=%10.4f  mean S2=%8.3f  bound_nontrivial(<1000)=%s  mean<=bound: %s'
          % (B, float(bound), mean, float(bound) < 1000, mean <= float(bound)))

    # named objects
    p('## Named objects (Run A)')
    for name in named_names:
        s = R[name]
        p('   %s:' % name)
        p('     S1 =', [s['S1_%d' % B] for B in BS])
        p('     S2 =', [s['S2_%d' % B] for B in BS2])
        p('     S3 =', s['S3'], ' Phi first', s['_phi_first'], ' last', s['_phi_last'], ' #digits in {0,n}:', s['_phi_extreme'])
        p('     max q_{k+1}/q_k over certified convergents near/above 2Q_1001: %.3f' % (s['_cf_maxratio_num'] / 1000))
        p('     S4 =', ['%.4f' % (s['S4num_%d' % B] / nks) for B in BS])
        p('     CF certified convergents: %d (max log10 q = %.1f)' % (s['_cf_len'], s['_cf_maxq_log10']))

    # O values
    Oref = {y: O(y)[0] for y in refnames}
    maxOref = max(Oref.values())
    hist = {}
    for v in Oref.values():
        hist[v] = hist.get(v, 0) + 1
    p('## Leave-one-out outside-range counts O(y); #statistics =', len(keys))
    p('   reference: max O =', maxOref, ' histogram', dict(sorted(hist.items())))
    Onamed = {}
    for name in named_names:
        c, which = O(name)
        Onamed[name] = c
        p('   O(%s) = %d  %s' % (name, c, which[:12]))

    # ---- verdict logic ----
    p('## Gates')
    # v1
    v1 = True
    for name, Br in (('6-e', 1), ('11/2-e', 2), ('17/3-e', 3)):
        s = R[name]
        mult = [B for B in BS if B % Br == 0]
        iii = s['S3'] == len(WP)
        i_ = all(s['S1_%d' % B] == len(W) for B in mult)
        ii = all(s['S2_%d' % B] == len(W) for B in mult if B in BS2)
        # also: non-multiples should NOT show (i)
        nonmult_i = [B for B in BS if B % Br and s['S1_%d' % B] == len(W)]
        p('   v1 %s (B_r=%d): (iii) %s ; (i) on multiples %s ; (ii) on multiples<=22 %s ; non-multiples with (i): %s'
          % (name, Br, iii, i_, ii, nonmult_i))
        v1 = v1 and iii and i_ and ii
    v2 = all(Onamed[n] <= maxOref for n in ('exp(sqrt2)', 'cos1', 'sqrt2'))
    p('   v1 =', v1, '; v2 =', v2, '(O controls', [Onamed[n] for n in ('exp(sqrt2)', 'cos1', 'sqrt2')], '<= maxOref', maxOref, ')')
    s = R['pi']
    r1i = [B for B in BS if s['S1_%d' % B] == len(W)]
    r1ii = [B for B in BS2 if s['S2_%d' % B] == len(W)]
    r1iii = s['S3'] == len(WP)
    lo3, hi3 = rng('S3')
    r2a = Onamed['pi'] > maxOref
    r2b = (s['S3'] < lo3 or s['S3'] > hi3) and s['S3'] >= hi3
    p('   r1: (i) B=%s ; (ii) B=%s ; (iii) %s' % (r1i, r1ii, r1iii))
    p('   r2: O(pi)=%d > maxOref=%d : %s ; S3(pi)=%d vs ref range [%d,%d] high-side outlier: %s'
      % (Onamed['pi'], maxOref, r2a, s['S3'], lo3, hi3, r2b))
    if INVALID_PREC or not v1 or not v2:
        verdict = 'INVALID'
    elif r1i or r1ii or r1iii or r2a or r2b:
        verdict = 'REFUTED'
    else:
        verdict = 'PASS'
    p('## SPEC-LITERAL VERDICT (spec gates as written, with skeptic precision fix):', verdict)

    # ---------------- skeptic diagnostics and corrected gate ----------------
    p('## Diagnostic D1: sqrt2 has bounded partial quotients (CF [1;2,2,2,...]).')
    p('   Lemma: if q_{k+1}/q_k <= rho for all large k, every interval [a, rho*a] (a large) contains a')
    p('   convergent denominator; strip S(j,B) has ratio j/(2B^2) >= 1001/(2B^2). Hence S2_B(sqrt2)=0')
    p('   whenever 1001/(2B^2) >= rho. Observed max ratio for sqrt2: %.3f' % (R['sqrt2']['_cf_maxratio_num'] / 1000))
    rho = R['sqrt2']['_cf_maxratio_num'] / 1000 + 0.001
    forced = [B for B in BS2 if 1001 / (2 * B * B) >= rho]
    p('   B with forced S2_B(sqrt2)=0 :', forced, '; observed S2(sqrt2)=0 at', [B for B in BS2 if R['sqrt2']['S2_%d' % B] == 0])
    p('   reference min S2_B for those B (B>=2 is >0 => sqrt2 is forced outside the range):', [rng('S2_%d' % B)[0] for B in forced])
    p('   => gate v2 as written MUST fail for sqrt2, independently of pi: spec defect.')
    p('## Diagnostic D2: S3 blind spot -- #factorial digits in {0,n} over W\' (2000 digits):')
    p('   ', {n: R[n]['_phi_extreme'] for n in named_names}, '; reference max =', max(R[y]['_phi_extreme'] for y in refnames))
    p('   cos1 = sum (-1)^k/(2k)! has a lacunary factorial expansion, yet S3(cos1) is in range: S3 tests only digit 1.')
    p('## Diagnostic D3: signature (ii) is not B-specific for the positive controls:')
    for name, Br in (('6-e', 1), ('11/2-e', 2), ('17/3-e', 3)):
        p('   %s: B (non-multiples of B_r) with S2_B=1000: %s' % (name, [B for B in BS2 if B % Br and R[name]['S2_%d' % B] == len(W)]))
    v2c = all(Onamed[n] <= maxOref for n in ('exp(sqrt2)', 'cos1'))
    p('## Corrected gate v2* (sqrt2 removed from v2, kept as structural S2 control): v2* =', v2c)
    v2alt = all(Onamed[n] <= maxOref for n in ('exp(sqrt2)', 'cos1', 'cbrt2'))
    p('## Alternative v2** (sqrt2 replaced by cbrt2 = 2^(1/3), CF believed generic but unproven): O(cbrt2) = %d ; v2** = %s' % (Onamed['cbrt2'], v2alt))
    if INVALID_PREC or not v1 or not v2c:
        verdict2 = 'INVALID'
    elif r1i or r1ii or r1iii or r2a or r2b:
        verdict2 = 'REFUTED'
    else:
        verdict2 = 'PASS'
    p('## CORRECTED-SPEC VERDICT (precision fix + v2*):', verdict2, '; with v2** instead:', verdict2 if v2alt else 'INVALID')

    with open(__file__.replace('.py', '.out'), 'w') as fh:
        fh.write('\n'.join(log) + '\n')


if __name__ == '__main__':
    main()
