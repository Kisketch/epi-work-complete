<!-- LOG-ONLY / NON-CANONICAL / DO NOT CITE -->
# Round 1 queries (siege-judge). Five self-contained queries, Q-R1-01 .. Q-R1-05.

Judge note (provenance of the initial values). The tex lines 4515-4665 do not state the initial values of Q_j. The values used below, (Q_0,Q_1)=(1,1) and (P_0,P_1)=(1,3), are read from `epi_formal/EpiFormal/Classification.lean` (`Qsel` = `selPair 1 1`, `Psel` = `selPair 1 3`; recurrence `Qsel_rec'` for j>=1). They are author-code values, not re-run, and not located in the paper text by this judge (Grep was unavailable). A worker should check them by hand: Q = 1,1,7,71,1001 and P = 1,3,19,193,2721, and the determinant P_j Q_{j+1} - P_{j+1} Q_j = 2(-1)^{j+1}.

Honesty overlay for every query: AGENTS.md applies. Label every result with one of the 5 categories (unconditional new / conditional / equivalent rewriting / finite computation / literature check). Mark paper-self-reported Lean claims "author-reported, not re-run". No numerical claim may be given from mental arithmetic. Do not cite Carella, Sarich or Foukzon as proof of anything. The irrationality of e+pi is an OPEN problem; any claimed proof of it must be treated as almost certainly wrong and re-audited line by line before being reported.

---

## Q-R1-01 (blueprint N3/N4): rational span of the lattice and the equivalence of P1 with linear independence of 1, e, pi

### Definitions (self-contained)
- e = 2.71828... is Euler's number. Allowed fact: e is irrational (you may use this without proof). You may NOT use the transcendence of e or pi, nor the transcendence of pi, nor anything about e+pi.
- L := Z + Z*(e+1)/2 = { a + b(e+1)/2 : a, b in Z }, a subset of R.
- For B a positive integer, B^{-1} L := { x in R : B x in L }.
- P1 is the statement: for every integer B >= 1, B*pi is not in L. (pi is the circle constant.)
- (The sequences Q_j, the norm ||.|| and F_tau play no role in this query. For completeness: ||y|| is the distance from y to the nearest integer; Q_0=Q_1=1, Q_{j+1}=(4j+2)Q_j+Q_{j-1} for j>=1; F_tau = { x in [0,1] : ||Q_j x|| = O(j^{-tau}) }.)

### The paper's text to audit (verbatim, Proposition prop:rational-span)
"For L = Z + Z(e+1)/2 one has  union_{B>=1} B^{-1}L = Q + Q e, B in N. Thus P1 is equivalent to linear independence of 1,e,pi over Q.
Proof. Each B^{-1}L lies in Q+Qe. Conversely, for x = r+se with r,s in Q, choose B>=1 clearing both denominators. Then Bx = B(r-s) + 2Bs(e+1)/2 in L. Since e is irrational, every nontrivial rational relation among 1,e,pi has a nonzero pi-coefficient and can be solved for pi. This proves the assertion. In particular B(e+pi)=A implies B pi = (A+B) - 2B(e+1)/2 in L directly."

### Task
(a) Give a complete, rigorous proof that the union over B>=1 of B^{-1}L equals Q + Qe (both inclusions; state precisely what "clearing denominators" must achieve so that B(r-s) and 2Bs are integers).
(b) Give a complete, rigorous proof that P1 is equivalent to: 1, e, pi are linearly independent over Q. Prove both directions separately. Show exactly where the irrationality of e is used and where the nonvanishing of the pi-coefficient comes from. Check the final sentence of the paper's proof, and report any gap, imprecision or hidden hypothesis in the paper's text (for instance, the case where the relation has pi-coefficient zero, the case of the zero relation, whether "nontrivial" is defined).
(c) State explicitly that this result does NOT advance the open problem (it is an equivalent rewriting, category 3), and that P1 itself is unproved.

Complete answer = a written proof of (a) and of (b) in both directions with every step justified from the allowed fact "e is irrational", a list of every gap or imprecision in the paper's quoted proof (or the statement "none found" with the reason), and the explicit category label "equivalent rewriting, no progress on P1". Anything less (for example only a sketch, or only one direction) is incomplete.

---

## Q-R1-02 (blueprint N5, upper bound): audit of dim_H F_tau <= max(1-tau, 0)

### Definitions (self-contained)
- Integer sequence (Q_j), j>=0: Q_0 = 1, Q_1 = 1, and Q_{j+1} = (4j+2) Q_j + Q_{j-1} for all j>=1. (So Q = 1, 1, 7, 71, 1001, ... Verify by hand or by code.)
- ||y|| = distance from the real number y to the nearest integer; so 0 <= ||y|| <= 1/2.
- For tau >= 0:  F_tau = { x in [0,1] : ||Q_j x|| = O(j^{-tau}) as j -> infinity }, i.e. there are C>0 and N such that ||Q_j x|| <= C j^{-tau} for all j >= N.
- dim_H = Hausdorff dimension. Claim to be audited (paper's Theorem thm:eventual-dimension): dim_H F_tau = max(1-tau, 0). This query concerns ONLY the upper bound dim_H F_tau <= max(1-tau,0).

### The paper's proof text for the upper bound (verbatim)
"The case tau=0 follows from ||y|| <= 1/2. The recurrence gives 4j+2 <= Q_{j+1}/Q_j <= 4j+3, and hence log Q_j = j log j + O(j) by summation. First fix 0 < tau <= 1. For positive integers C,N, require ||Q_j x|| <= C j^{-tau} at every j >= N. At level j the allowable intervals have centres k/Q_j and radius r_j = C j^{-tau}/Q_j. Each meets at most 1 + 2(r_j + r_{j+1}) Q_{j+1} = O_C(j^{1-tau}) next-level intervals, by counting grid points in the enlarged parent. The number of chains through level n is therefore at most exp((1-tau) n log n + O_{C,N}(n)). For s > 1-tau, multiplying this bound by (2 r_n)^s gives a quantity tending to zero. Countable union over C,N yields the upper bound. [...] For tau >= 1, use 0 in F_tau subset F_1."
(The last sentence belongs to the paper's lower-bound paragraph; it is quoted because it is used to cover tau >= 1 for the full theorem. For the upper bound, check that tau >= 1 is covered by the case tau = 1, including the claim F_tau subset F_1 for tau >= 1.)

### Task
Check the upper-bound proof line by line, or re-prove the upper bound independently. Specifically verify or refute each of: (i) 4j+2 <= Q_{j+1}/Q_j <= 4j+3 for all j>=1 (is the upper bound 4j+3 right for small j, and does it need Q_{j-1}/Q_j <= 1 and how?); (ii) log Q_j = j log j + O(j); (iii) the description of F_tau as a countable union over (C,N) of sets E_{C,N} = { x : ||Q_j x|| <= C j^{-tau} for all j >= N }, and that E_{C,N} is covered, for each n >= N, by the level-n intervals [k/Q_n - r_n, k/Q_n + r_n]; (iv) the child-count bound 1 + 2(r_j + r_{j+1}) Q_{j+1} for the number of centres k'/Q_{j+1} within r_j + r_{j+1} of a centre k/Q_j, including the exact reason that nonempty intersection of the two intervals forces |k'/Q_{j+1} - k/Q_j| <= r_j + r_{j+1}; (v) that this is O_C(j^{1-tau}) for 0<tau<=1 (check the term 2 r_j Q_{j+1} = 2 C j^{-tau} Q_{j+1}/Q_j and the term 2 r_{j+1} Q_{j+1}); (vi) the number of level-N starting intervals (about Q_N + 1) and its effect on the O_{C,N}(n) term; (vii) the chain count exp((1-tau) n log n + O(n)); (viii) the final Hausdorff-sum estimate: with s > 1-tau, show count(n) * (2 r_n)^s -> 0, tracking the exponent of Q_n precisely (r_n^s ~ Q_n^{-s} n^{-tau s}, log Q_n = n log n + O(n)); (ix) the case tau = 1 (max(1-tau,0)=0) and that dimension 0 for tau=1 requires s>0 arbitrary; (x) the case tau = 0.
Report EVERY gap, inaccuracy or unjustified step, however small, with its exact location, and state whether it is fatal or repairable. If you find the argument correct, say so and give your own independent justification for (iv), (vii), (viii).

Complete answer = a verdict (correct / correct with repairable gaps / incorrect) on the upper-bound proof, a numbered list of all gaps with locations and repairs (or "none found" plus your independent proof of (iv), (vii), (viii)), and the label "unconditional proof on paper, elementary covering argument; likely not new beyond standard Hausdorff-dimension lacunary-sequence results unless a literature check says otherwise (literature check not done)". Anything less is incomplete.

---

## Q-R1-03 (blueprint N5, lower bound): audit of the mass-distribution proof for 0 < tau < 1

### Definitions (self-contained)
- (Q_j), j>=0: Q_0 = 1, Q_1 = 1, Q_{j+1} = (4j+2) Q_j + Q_{j-1} for j>=1 (Q = 1, 1, 7, 71, 1001, ...).
- ||y|| = distance from y to the nearest integer.
- F_tau = { x in [0,1] : ||Q_j x|| = O(j^{-tau}) }, tau >= 0. Claim: dim_H F_tau = max(1-tau, 0). This query concerns ONLY the lower bound for 0 < tau < 1: dim_H F_tau >= 1 - tau.
- Notation: r_j = C j^{-tau}/Q_j (the radius of the level-j intervals centred at k/Q_j, k an integer).

### The paper's proof text for the lower bound (verbatim)
"The recurrence gives 4j+2 <= Q_{j+1}/Q_j <= 4j+3, and hence log Q_j = j log j + O(j) by summation. [...] For 0<tau<1 take C=1/8 and start with one interval inside (0,1) at a sufficiently large level N. Each retained parent contains at least 2(r_j - r_{j+1}) Q_{j+1} - 1 whole child intervals. This is bounded below by c j^{1-tau} with an absolute c>0 for all sufficiently large j. Choose exactly b_j = floor(c j^{1-tau}) >= 2 children per parent. The nested intersection lies in F_tau. Give the children equal shares of their parent's mass. Each level-n interval then has mass 1/M_n, where M_n = prod_{j=N}^{n-1} b_j and log M_n = (1-tau) n log n + O(n). For an interval of length Q_{n+1}^{-1} <= h < Q_n^{-1}, the level-n grid spacing and 2 r_n < Q_n^{-1} imply that it meets at most three retained intervals. Its mass is at most 3/M_n. For every 0 < s < 1-tau, the growth estimates give 3/M_n <= Q_{n+1}^{-s} <= h^s for all large n. Summing over any sufficiently fine interval cover of the intersection shows its s-dimensional Hausdorff measure is positive. Letting s increase to 1-tau proves the lower bound."

### Task
Audit line by line, or reprove, the lower bound. Specifically decide, with full justification:
(i) Is "each retained parent contains at least 2(r_j - r_{j+1}) Q_{j+1} - 1 whole child intervals" correct? Define a whole child interval as [k'/Q_{j+1} - r_{j+1}, k'/Q_{j+1} + r_{j+1}] contained in the parent [k/Q_j - r_j, k/Q_j + r_j]. Count the integers k' with k'/Q_{j+1} in [k/Q_j - r_j + r_{j+1}, k/Q_j + r_j - r_{j+1}] (an interval of length 2(r_j - r_{j+1})) and state the exact lower bound (is it 2(r_j - r_{j+1})Q_{j+1} - 1, or something else, given that the count of integers in a closed interval of length L is at least floor(L) >= L - 1 and at most L+1?). Also check that k/Q_j itself is a grid point k Q_{j+1}/Q_j / Q_{j+1} with Q_{j+1}/Q_j not nec. an integer, so the child grid is not aligned with the parent centre.
(ii) The positivity and sign of 2(r_j - r_{j+1})Q_{j+1}: r_j - r_{j+1} = C j^{-tau}/Q_j - C (j+1)^{-tau}/Q_{j+1}. Since Q_{j+1} >= (4j+2) Q_j, show r_{j+1} is much smaller than r_j and that 2(r_j - r_{j+1})Q_{j+1} >= c' j^{1-tau} for large j with an explicit absolute c'. Is the claimed constant "absolute c>0" independent of C and of j? Compute the limit of j^{-(1-tau)} 2(r_j - r_{j+1}) Q_{j+1} as j -> infinity for C=1/8 using Q_{j+1}/Q_j ~ 4j; is it positive? State the actual value (this limit must be computed by an argument, and numerically confirmed with code, not by mental arithmetic).
(iii) Consistency of the choice C = 1/8 with the radius r_j = C j^{-tau}/Q_j: the paper later requires 2 r_n < Q_n^{-1}. Check whether 2 r_n = 2 C n^{-tau}/Q_n = (1/4) n^{-tau}/Q_n < 1/Q_n holds for every n >= 1 and tau > 0, and state whether the constant C=1/8 plays any further role (is any smaller or larger C equally good? which requirement forces an upper limit on C, which forces a lower limit?).
(iv) Does the nested intersection lie in F_tau? (Level-j intervals centred at k/Q_j with radius r_j give ||Q_j x|| <= Q_j r_j = C j^{-tau}; check this inequality, including that "start with one interval inside (0,1)" gives points in [0,1].)
(v) The mass: equal shares gives mass 1/M_n; check log M_n = (1-tau) n log n + O(n) from b_j = floor(c j^{1-tau}) >= 2 (when is b_j >= 2?).
(vi) "meets at most three retained intervals": an interval I of length h with Q_{n+1}^{-1} <= h < Q_n^{-1}. Level-n retained intervals have centres on the grid (1/Q_n)Z and diameter 2 r_n < Q_n^{-1}. Count exactly how many level-n retained intervals I can meet: is it at most 2 (since h < Q_n^{-1} and the retained intervals are disjoint-separated by gaps of at least Q_n^{-1} - 2 r_n) or at most 3, and is the paper's "three" valid (give a proof or counterexample)?
(vii) Verify 3/M_n <= Q_{n+1}^{-s} for large n, for every 0 < s < 1-tau, from log M_n = (1-tau) n log n + O(n) and log Q_{n+1} = (n+1) log(n+1) + O(n).
(viii) Complete the mass distribution principle: state the principle used (mu(I) <= K |I|^s for all intervals I of length below some h_0 implies H^s(support) >= mu(support)/K > 0), check that the case h < Q_n^{-1} vs Q_{n+1}^{-1} <= h covers all small h (the intervals [Q_{n+1}^{-1}, Q_n^{-1}) partition (0, Q_N^{-1}) because Q_j increases to infinity), and that mu is a genuine Borel probability measure supported on the nested intersection.
(ix) The cases tau = 0 and tau >= 1 as stated ("0 in F_tau subset F_1" covers tau >= 1 only for the lower bound max(1-tau,0)=0, which is trivial).
Report EVERY gap with its location and whether fatal or repairable. If the stated constants "at least 2(r_j - r_{j+1})Q_{j+1} - 1 whole child intervals" or "at most three" are wrong or only true with caveats, say so and give the corrected statement and the corrected argument. Any numerical claim must be backed by code and its output quoted.

Complete answer = a verdict (correct / correct with repairable gaps / incorrect) on the lower-bound proof, explicit answers to (i)-(ix) with proofs, the value of the limit in (ii), the verdict on C=1/8 versus r_j = C j^{-tau}/Q_j in (iii), a list of all gaps with repairs, and the label "unconditional proof on paper, elementary mass distribution argument; novelty unchecked". Anything less is incomplete.

---

## Q-R1-04 (blueprint N6 core, blind attack): prove or disprove "pi is not in Q + Q e"

### Definitions (self-contained)
- e = 2.71828... (Euler's number), pi = 3.14159... (circle constant). Q + Qe = { r + s e : r, s rational }.
- Equivalent form (proved on paper in the project; you may use it): pi is not in Q + Qe  if and only if  1, e, pi are linearly independent over Q  if and only if  for every integer B >= 1, B*pi is not in L := Z + Z(e+1)/2.
- Relevant structure (you may use or ignore): Q_0=Q_1=1, Q_{j+1}=(4j+2)Q_j+Q_{j-1} (j>=1), the denominators of selected continued-fraction-type convergents P_j/Q_j of e with P_0=1, P_1=3, same recurrence, determinant P_jQ_{j+1}-P_{j+1}Q_j = 2(-1)^{j+1}. ||y|| = distance to the nearest integer. The project proved on paper (Lean author-reported, not re-run) that for x not in L, limsup_j j||Q_j x|| >= 1/4; so P1 reduces to the sparse lower bound limsup_j j||B Q_j pi|| > 1/8 for every B>=1.

### Mandatory statement
This is a WELL-KNOWN OPEN PROBLEM. It is equivalent to: no nontrivial rational linear relation among 1, e, pi. It implies the irrationality of e+pi, e-pi, and pi/e... (each open). It is not expected to be solvable. The known hard fact is only that at least one of e+pi, e*pi is transcendental (from the transcendence of e and pi; category 1 literature fact, easy). Do NOT cite or rely on Carella, Sarich or Foukzon, or on any claimed proof of the irrationality of e+pi (these are not accepted by the community and are forbidden as sources). Do not cite unverified 2026 preprints as established facts.

### Task
State at the top of your answer that this is a well-known open problem. Then attempt it honestly (any route: continued fractions of pi and e, Baker/Nesterenko type methods, Pade approximation, Schanuel, E-functions and G-functions, 1-motives, Hermite-type constructions, the project's Q_j-sequence reduction, the Dirichlet/Minkowski lattice route, anything). For each attempted route give its precise form and the exact point at which it fails (the missing lemma, the wrong inequality direction, the hypothesis that is unproved, the circularity). Classify EACH failure with exactly one label from this taxonomy: route error / granularity error / formalization-interface error / missing literature / missing certificate / context drift / premature convergence / Lean unreachable. If any route appears to succeed, treat it as almost certainly wrong, re-audit every line, and report it as "claimed proof, unverified" with the check list you performed. State the category (1-5 of AGENTS.md) of every partial result. Do not call anything a breakthrough.

Complete answer = EITHER a complete rigorous proof (every inference justified, using only established theorems that you name and whose statements you quote correctly, flagged "claimed proof, unverified, requires adversarial audit"), OR a precise description of each attempted route with the exact point where it fails, each failure classified with the taxonomy above, plus an overall statement that the problem remains open and what was NOT achieved. A bare "I could not do it" without route-by-route failure points is incomplete.

---

## Q-R1-05 (blueprint N7 route audit): strongest unconditional provable statement about ||B Q_j pi||

### Definitions (self-contained)
- e = Euler's number, pi = circle constant. L := Z + Z*(e+1)/2 = { a + b(e+1)/2 : a,b in Z }.
- (Q_j), j>=0: Q_0 = 1, Q_1 = 1, Q_{j+1} = (4j+2) Q_j + Q_{j-1} for j>=1 (Q = 1, 1, 7, 71, 1001, ...). Companion (P_j): P_0=1, P_1=3, same recurrence; determinant P_j Q_{j+1} - P_{j+1} Q_j = 2(-1)^{j+1}; P_j/Q_j are convergents of e (3/1, 19/7, 193/71, 2721/1001, ...), and delta_j = Q_j e - P_j -> 0.
- ||y|| = distance from y to the nearest integer.
- F_tau = { x in [0,1] : ||Q_j x|| = O(j^{-tau}) }; the paper proves (on paper, being audited in Q-R1-02/03) dim_H F_tau = max(1-tau,0), in particular the set of x with limsup_j j||Q_j x|| < infinity has Hausdorff dimension 0.
- Project facts (author-reported; a worker must not rely on them unless proved or cited): for x not in L, limsup_j j||Q_j x|| >= 1/4 (the "classification gap"); and j||Q_j x|| -> 0 iff x in L.
- P1 (open): for every B >= 1, B*pi is not in L; equivalent to: 1, e, pi linearly independent over Q.

### Task
Find and prove, completely and unconditionally, the strongest statement you can about the sequence ||B Q_j pi|| (B >= 1 a fixed integer, j -> infinity) or more generally about ||B Q_j x||. Examples of acceptable targets (you choose; stronger is better, but it must be PROVED):
 (a) a lower bound on limsup_j j||B Q_j x|| valid for x outside a set of Lebesgue measure zero or of Hausdorff dimension zero (and say precisely which set; for example the dimension-zero set {x : limsup_j j||B Q_j x|| < infinity});
 (b) a statement valid for ALL x not in an explicit exceptional set (for example x not in B^{-1}L: limsup_j j||B Q_j x|| >= 1/4, with a full proof from the recurrence and the convergence of P_j/Q_j to e);
 (c) a metric statement for almost every x (for example liminf or limsup of j||B Q_j x|| or of ||B Q_j x||/psi(j)), proved via Borel-Cantelli / lacunarity of Q_j (Q_{j+1}/Q_j >= 4j+2);
 (d) any other unconditional, rigorous statement that is not a trivial consequence of ||y|| <= 1/2.
You must (1) state the theorem exactly, (2) prove it completely with every step justified, (3) give its category per AGENTS.md (a proof of a statement that the project already lists, such as the classification gap, is category 5 reproduction unless it genuinely strengthens it; a statement not in the literature is category 1 only after a literature check, which you must describe as "negative search only" with its coverage), and (4) state EXPLICITLY and rigorously why it does NOT imply P1, i.e. which specific condition, such as "pi not in B^{-1}L", or "pi outside the measure/dimension-zero exceptional set", is not verified for pi by your statement, and why a single point cannot be controlled by a measure or dimension statement.

Complete answer = a precisely stated theorem about ||B Q_j x|| (or ||B Q_j pi|| for all x not in an explicit set), a complete proof, its category label, and a rigorous explanation of why it does not imply P1 (e.g. that pi could lie in the exceptional set for all the statement says). A statement without a full proof, or a statement that claims to imply P1 without a verified step, is incomplete.
