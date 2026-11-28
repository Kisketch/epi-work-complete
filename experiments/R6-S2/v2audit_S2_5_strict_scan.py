"""v2audit_S2_5: enumerate every strict inequality ('<' or '>' inside $...$, plus open intervals
'(A_k,A_k+2)') in proofs/R6-S2.md, with the auditor's per-occurrence verdict attached.
Verdicts were made by hand-reading each occurrence; numerical sub-claims are covered by
v2audit_S2_3 / S2_4. Any occurrence without a verdict is flagged UNREVIEWED."""
import os, re
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
lines = open(os.path.join(ROOT, "proofs", "R6-S2.md"), encoding="utf-8").read().splitlines()
V = {
 26: "statement text (K<inf hypothesis) - not a claim",
 43: "prose only ('对 k>=k_1 ...'), no math strict sign in $ $ besides k<k_1 index range - OK",
 53: "quotes Lemma 0 hypothesis '<theta_n/4' - OK",
 77: "alpha_m > a_m >= 1: strict since 1/alpha_{m+1} > 0 for an infinite CF - OK",
 86: "theta_n < 1/a_{n+1}: from alpha_{n+1} > a_{n+1} and q_{n-1}/q_n >= 0 - OK; |eps_n| < 1/q_{n+1}: q_n alpha_{n+1}+q_{n-1} > q_{n+1} since q_n>=1 - OK",
 89: "denominator > 0 - OK",
 90: "same as 86 - OK",
 95: "D4(ii) index set j>k - not an inequality claim",
 117: "i<ell case split - index only",
 123: "Lemma B statement: open interval (A_k,A_k+2), proven at L126 - OK",
 126: "0<1/alpha_{n_k+2}<1 (alpha_{n_k+2} > a_{n_k+2} >= 1, also for ell=0 where a_{n_k+2}=A_{k+1}); open interval (A_k,A_k+2); A_k theta in (A_k/(A_k+2),1) - OK; checked exactly in S2_3",
 128: "alpha_{n_{k+1}+1} > A_{k+1} - OK",
 129: "i<ell - index only",
 141: "hypothesis strict - OK (n*-1 >= 0 since n*>=1)",
 143: "limsup<1/4 => R_n<1/4 eventually - OK",
 147: "theta_{n+-1}<1, a_{n+1}theta_n<1 from D2 (n-1>=0) - OK",
 148: "|m_n| < 3/4: first '<' from strict hypothesis at n-1,n,n+1 >= n*-1; second from D2 - OK (sup ~2.994/4 seen in S2_3)",
 157: "K<inf hypothesis - not a claim",
 162: "(K+1)theta < (K+1)/A_k: K+1>0 and theta<1/A_k strict - OK",
 173: "choice of k_1 (dist<1/2) - definition, OK because dist -> 0",
 175: "|K g_k| < 1/2 - restates 173, OK",
 178: "dist<1/2 for k>=k_1 - OK",
 179: "k<k_1 index range - OK",
 193: "0<A_k theta<1 (Lemma B1 open interval) - OK; |t_k|<K+1 strict for k>=k_0 since A_k theta<1 and K+1>0 - OK; '<=' used when y=0 - OK",
 204: "|u eps_n|<1/2 for large n: |u eps_n|<=|u|/q_{n+1}->0 - OK; '<inf' - OK",
 208: "theta limit c c'/K > 0 - OK",
 210: "R_n<1/4 eventually from R_n->0 - OK",
 214: "T_max<inf from bounded tau - OK",
 219: "|eps_{n_k}|<1/q_{n_k+1} (D2) - OK",
 226: "index range j>k - OK",
 241: "q_{n_j}|eps_n| < q_{n_j}/q_{n+1}, q_n|eps_{n_j}|<q_n/q_{n_j+1} - strict since q>=1 - OK",
 243: "remark on degeneracy: strict forms fail only when T_max=0 (resp T'_max=0); example T_max>0,T'_max=0 verified by hand: r_1=0,T_1=-sigma r~_0 (needs r~_0 != 0), r_k=0 for k>=2 - OK",
 246: "j<k index - OK",
 247: "'< 4T_max q_{n_{k-1}}/q_{n_k+1}' strict needs T_max>0 (covered by 243); k=1 empty sum not stated explicitly (immaterial, only k->inf used) - MINOR editorial",
 248: "'< 4T_max q_{n_k}/q_{n_{k+1}+1}' strict needs T_max>0 (243) - OK",
 254: "'<' needs T_max>0 (243) - OK",
 255: "'<' needs T_max>0 (243); n<n_{k+1} - OK",
 257: "|K g'_k|<1/2 for large k; dist<1/2 => unique nearest integer - OK",
 260: "|K g'_k|<1/2 condition - OK",
 271: "|t|>1 => cost>1 - OK",
 275: "0<=a<b<=L-1 index - OK",
 286: "K<inf case split - OK",
 302: "k_2<=k<k' index - OK",
 311: "K<inf conclusion of S1(d) part (d4) - OK",
 312: "K<inf - OK",
}
pat = re.compile(r"\$[^$]*\$")
unrev = 0; total = 0
for i, l in enumerate(lines, start=1):
    maths = pat.findall(l)
    hits = [m for m in maths if re.search(r"(?<![-\\])[<>]|\\lt|\\gt", m.replace("\\to", ""))]
    if re.search(r"\(A_k,A_k\+2\)", l): hits.append("(A_k,A_k+2) open interval")
    if not hits: continue
    total += 1
    verdict = V.get(i)
    if verdict is None: unrev += 1; verdict = "UNREVIEWED"
    print(f"L{i}: {len(hits)} strict-sign math span(s): {[h[:70] for h in hits][:4]}")
    print(f"     verdict: {verdict}")
print("lines with strict signs:", total, " unreviewed:", unrev)
