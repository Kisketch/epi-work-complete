r"""E17 (v4 brief, 2026-11-25): upgrade Hypothesis hyp:tail to proved lemmas.

Applies the exact replacements dictated in
verification/flash_task_briefs_v4_20261125.md to:
  paper2_spectral_gap_dimension/split/src_sections/sec-critical-scaling.tex
  paper2_spectral_gap_dimension/split/frontmatter-2C-v3-20261124.tex
  paper2_spectral_gap_dimension/BUILD_LOG_20261124.md (append one line)

Every replacement asserts the old text occurs exactly once before applying.
Only the session-created files are touched; no repository original is modified.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SEC = ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections" / "sec-critical-scaling.tex"
FM = ROOT / "paper2_spectral_gap_dimension" / "split" / "frontmatter-2C-v3-20261124.tex"
LOG = ROOT / "paper2_spectral_gap_dimension" / "BUILD_LOG_20261124.md"


def rep(s: str, old: str, new: str, what: str) -> str:
    n = s.count(old)
    assert n == 1, f"[{what}] expected 1 occurrence, found {n}"
    return s.replace(old, new)


s = SEC.read_text(encoding="utf-8")

# ---- Step 1: header status tags ------------------------------------------
s = rep(
    s,
    "%   Theorem~\\ref{thm:critical-scaling} [CONDITIONAL] proved modulo hypothesis (H).\n"
    "%   Corollary~\\ref{cor:critical-exp} [CONDITIONAL] consequence of (H).",
    "%   Lemma~\\ref{lem:resolvent-uniform} [THEOREM] proved here (elementary estimates).\n"
    "%   Lemma~\\ref{lem:master}       [THEOREM] proved here modulo the repo criterion.\n"
    "%   Theorem~\\ref{thm:critical-scaling} [THEOREM] proved here modulo the repo criterion.\n"
    "%   Corollary~\\ref{cor:critical-exp} [THEOREM] consequence of the Theorem.",
    "step1",
)

# ---- Step 2: replace the Hypothesis remark with two lemmas ---------------
OLD_HYP = """\\begin{remark}[Hypothesis: uniform tail equation in the critical window]\\label{hyp:tail}
There are $\\delta>0$ and $m_0$ such that, for all $m\\ge m_0$ and all
$\\varepsilon\\in(0,m^{-1/2+\\delta}]$, the Hausdorff dimension
$s:=\\dimH F_{m,S,B}$ satisfies
\\begin{equation}\\label{eq:tail-uniform}
d\\,C_S(1+\\varepsilon)\\left(\\frac1\\varepsilon+\\gamma+O(\\varepsilon)+O(m^{-1})\\right)
m^{-1-\\varepsilon}=1+O(m^{-1/2}),
\\end{equation}
where $\\varepsilon:=2s-1$ and the $O$-constants are absolute (independent of $m$
and of $\\varepsilon$ in the stated range).
\\end{remark}"""

NEW_LEMMAS = r"""\begin{lemma}[Uniform two-sided resolvent expansion]\label{lem:resolvent-uniform}
Let $m\ge 2(\max S+\max B+1)$, put $\Sigma:=1+\max S+\max B$, and write
$h(s):=d\,C_S(2s)\,m^{-2s}\,\zeta(2s)$ for $s\in(\max(s_0,\tfrac12),1]$.
Then for every such $s$ and every $x\in[0,1]$,
\begin{equation}\label{eq:resolvent-uniform}
\mathcal L_{s,\mathcal A_{m,S,B}}V_{S,s}(x)
=V_{S,s}(x)-1+h(s)\,(1+\rho(s,x)),\qquad |\rho(s,x)|\le C_0\,\Sigma/m,
\end{equation}
where $C_0$ is an absolute constant.
\end{lemma}

\begin{proof}
The $S$-branches contribute $V_{S,s}(x)-1$ by the multi-branch resolvent
identity \eqref{eq:multi-resolvent-branch} (valid for $s>s_0(S)$).  Each of the
$d$ large-branch families ($a=r+km$, $r\in S$, $k\ge1$; and $a=km-b$, $b\in B$,
$k\ge1$) is handled identically.  Write $a+x=m(k+\theta)$ with
$|\theta|\le\Sigma/m\le\tfrac12$; the Hurwitz shift obeys
$\sum_{k\ge1}\bigl[(k+\theta)^{-2s}-k^{-2s}\bigr]
\le 2s\,2^{2s+1}\,|\theta|\,\zeta(2s+1)\le C\,\Sigma/m$, the constant being
absolute because $u\,\zeta(1+u)$ is bounded on $(0,2]$; and the test-function
expansion $|V_{S,s}(y)-C_S(2s)|\le 2s\,y\,C_S(2s)$ (mean value theorem over
each word, using $p(w)/q(w)=[0;w]\le1$) contributes a relative error
$O\bigl(m^{-1}\zeta(2s+1)/\zeta(2s)\bigr)=O(\Sigma/m)$, since
$\zeta(2s)\ge1$ on $2s>1$.  Summing the $d$ families gives
\eqref{eq:resolvent-uniform}.
\end{proof}

\begin{lemma}[Master equation at the critical dimension]\label{lem:master}
Under the assumptions of Lemma~\ref{lem:resolvent-uniform}, let
$s^*:=\dimH F_{m,S,B}$ and $\varepsilon_m:=2s^*-1$.  Then
\begin{equation}\label{eq:master}
\bigl|\,d\,C_S(1+\varepsilon_m)\,m^{-1-\varepsilon_m}\,\zeta(1+\varepsilon_m)-1\,\bigr|
\le \bar\delta_m:=C_1\,\Sigma/m+2\,\ee^{-c_0m^2},
\end{equation}
where $c_0:=d\,C_S(2)/3>0$ and $C_1$ is absolute.
\end{lemma}

\begin{proof}
The function $h$ is finite, continuous and strictly decreasing on
$(\max(s_0,\tfrac12),1]$, tends to $+\infty$ at the left endpoint (through the
pole of $C_S$ at $2s_0$ or of $\zeta$ at $1$), and $h(1)<1$ for all large $m$
(the quantitative pole bound $C_S(2(s_0+\delta))\le 32/\delta$ used in
Theorem~\ref{thm:multi-residue-asymptotic}(v) gives $h(1)\le 64\,d\,\zeta(2)/m^2$).

\emph{Upper side.}  If $h(s)(1+C_0\Sigma/m)\le1$, then
\eqref{eq:resolvent-uniform} makes $V_{S,s}$ a subsolution,
$\mathcal L_{s,\mathcal A}V\le V$, whence $\dimH F_{m,S,B}\le s$ by the upper
direction of the transfer-operator criterion of
Theorem~\ref{thm:residues-general}(ii) (kernel-checked as
\texttt{step\_cert\_upper\_sound}; the paper's own proof of part~(i) applies
this direction to $V_{S,s}$ itself).  Consequently
$h(s^*)\ge1/(1+C_0\Sigma/m)$.

\emph{Lower side.}  Put $K:=\lceil\ee^{m^3}\rceil$,
$D_K:=S\cup\{r+km:\ r\in S,\ 1\le k\le K\}\cup\{km-b:\ b\in B,\ 1\le k\le K\}
\subseteq\mathcal A_{m,S,B}$ (a finite subalphabet) and
$h_K(s):=d\,C_S(2s)\,m^{-2s}\sum_{k\le K}k^{-2s}$.  The truncated test function
$v_N:=\sum_{j<N}\mathcal L_{s,S}^{\,j}1$ satisfies
$\mathcal L_{s,S}v_N=v_N-1+\mathcal L_{s,S}^{\,N}1\ge v_N-1$, and the $D_K$-tail
contributes $h_K(s)(1+O(\Sigma/m))$ by the estimates of
Lemma~\ref{lem:resolvent-uniform}; hence $\mathcal L_{s,D_K}v_N\ge v_N$
whenever $h_K(s)(1-C_2\Sigma/m)\ge1$, and the finite-subalphabet lower
direction of Theorem~\ref{thm:residues-general}(ii) (kernel-checked as
\texttt{step\_cert\_lower\_sound}) yields $\dimH F_{m,S,B}\ge s$.

It remains to compare $h_K$ with $h$.  Let $\varepsilon_0$ be the unique
solution of $h(\varepsilon_0)=1$.  Since
$f(\varepsilon):=d\,C_S(2)\,m^{-1-\varepsilon}/\varepsilon$ is a decreasing
lower bound for $h$ and $f(\varepsilon_0)\le h(\varepsilon_0)=1$, we get
$\varepsilon_0\ge c_0/m$ with $c_0=d\,C_S(2)/3$ for all large $m$ (the factor
$m^{-\varepsilon_0}\ge\tfrac12$ holds because $\varepsilon_0\log m\to0$).
Hence for all $\varepsilon\ge\varepsilon_0/2$ the truncation ratio obeys
$\mathrm{trunc}(\varepsilon):=\sum_{k>K}k^{-1-\varepsilon}/\zeta(1+\varepsilon)
\le C\,K^{-\varepsilon}\le C\,\ee^{-c_0m^2}$.  Moreover $h_K(\varepsilon_0)
=1-\mathrm{trunc}(\varepsilon_0)\le1$ together with $|h_K'|/h_K\ge2\log m$ (the
$m^{-2s}$ factor dominates) gives $|\varepsilon_K-\varepsilon_0|\le
C\ee^{-c_0m^2}/\log m$ for the $h_K$-root $\varepsilon_K$, so
$\mathrm{trunc}(\varepsilon_K)\le2C\ee^{-c_0m^2}$ as well.  The sandwich
$s_K\le s^*\le s_-$ between the two criteria and the monotonicity of $h$ now
give $h(s^*)\le h(s_K)\le(1-C_2\Sigma/m)^{-1}(1-\mathrm{trunc}(\varepsilon_K))^{-1}$,
which is \eqref{eq:master}.
\end{proof}"""

s = rep(s, OLD_HYP, NEW_LEMMAS, "step2")

# ---- Step 3: theorem / corollary statements -------------------------------
s = rep(
    s,
    "Assume Hypothesis~\\ref{hyp:tail}. Let $\\eta:=1-2s_0(S)$ and",
    "Let $\\eta:=1-2s_0(S)$ and",
    "step3a",
)
s = rep(
    s,
    "Assume Hypothesis~\\ref{hyp:tail} and let $s_0(S)=\\frac12$, i.e.\\ $\\eta=0$. Then",
    "Let $s_0(S)=\\frac12$, i.e.\\ $\\eta=0$. Then",
    "step3b",
)

# ---- Step 3c: rewrite the theorem proof body ------------------------------
OLD_PROOF = """\\begin{proof}
Put $\\varepsilon:=2\\dimH F_{m,S,B}-1$ and write
$\\varepsilon=m^{-1/2}u_m$, $\\eta=m^{-1/2}x_m$, so that $x_m\\to x$.
By Lemma~\\ref{lem:pole}(e),
\\[
C_S(1+\\varepsilon)=\\frac{\\kappa}{\\varepsilon+\\eta}+O(1)
=\\frac{\\kappa\\,m^{1/2}}{u_m+x_m}+O(1).
\\]
Substituting into \\eqref{eq:tail-uniform} and using
$1/\\varepsilon=m^{1/2}/u_m$ gives
\\[
d\\left(\\frac{\\kappa m^{1/2}}{u_m+x_m}+O(1)\\right)
\\left(\\frac{m^{1/2}}{u_m}+O(1)\\right)m^{-1-\\varepsilon}
=1+O(m^{-1/2}).
\\]
The main term equals
$\\dfrac{d\\kappa}{u_m(u_m+x_m)}\\,m^{-\\varepsilon}$; all remaining terms are
$O(m^{-1/2})$ times $m^{-\\varepsilon}$, because
$O(1)\\cdot m^{1/2}\\cdot m^{-1}=O(m^{-1/2})$ and
$O(1)\\cdot m^{1/2}/u_m\\cdot m^{-1}=O(m^{-1/2})$ (here $u_m$ stays bounded away
from $0$ and $\\infty$, as follows a posteriori from \\eqref{eq:scaling-limit};
the a priori bounds $u_m=O(1)$ and $u_m\\gg1$ are provided by
Theorem~\\ref{thm:multi-residue-asymptotic}(iv)--(v)). Since
$\\varepsilon\\to0$ we have $m^{-\\varepsilon}\\to1$, and therefore
\\[
\\frac{d\\kappa}{u_m(u_m+x_m)}\\longrightarrow1 .
\\]
Hence every limit point $u$ of $(u_m)$ satisfies $u(u+x)=d\\kappa$; the positive
root is $\\Phi(x)$, and the negative root is excluded because
$\\dimH F_{m,S,B}\\ge\\frac12$ (Theorem~\\ref{thm:multi-residue-asymptotic}(ii)).
Thus $u_m\\to\\Phi(x)$, which is \\eqref{eq:scaling-limit}.
\\end{proof}"""

NEW_PROOF = r"""\begin{proof}
\emph{A priori bounds.}  $\varepsilon_m>0$ since $\dimH F_{m,S,B}>\tfrac12$
(Theorem~\ref{thm:multi-residue-asymptotic}(ii)), and
$\varepsilon_m\le 2\max\bigl(-\eta,\,C\sqrt{d/m}\bigr)$ with $C$ absolute: at
$\bar\varepsilon:=2\max(-\eta,\,24\sqrt{d/m})$ the pole bound
$C_S(1+\varepsilon)\le64/(\varepsilon+\eta)$ and
$\zeta(1+\varepsilon)\le3/\varepsilon$ give $h(\bar\varepsilon)\le\tfrac16
<1/(1+\bar\delta_m)$, so $s^*$ lies below the $h$-threshold.  In particular
$\varepsilon_m\to0$ and $\varepsilon_m+\eta\to0$ along any sequence with
$m\to\infty$ and $\eta m^{1/2}\to x\in\R$.

\emph{The implicit equation.}  Lemma~\ref{lem:master} gives
$d\,C_S(1+\varepsilon_m)\,m^{-1-\varepsilon_m}\zeta(1+\varepsilon_m)
=1+O(\bar\delta_m)$.  Lemma~\ref{lem:pole}(e) rewrites
$C_S(1+\varepsilon_m)=\kappa/(\varepsilon_m+\eta)+O(1)$ (legitimate because
$\varepsilon_m+\eta\to0$), part~(iii) of
Theorem~\ref{thm:multi-residue-asymptotic} rewrites
$\zeta(1+\varepsilon_m)=\varepsilon_m^{-1}+\gamma+O(\varepsilon_m)$, and the
relative errors so introduced are
$O(\varepsilon_m+\eta)+O(\varepsilon_m)+O(\bar\delta_m)=o(1)$.  Hence
\begin{equation}\label{eq:implicit}
\varepsilon_m\,(\varepsilon_m+\eta)\,m^{1+\varepsilon_m}=d\,\kappa\,(1+o(1)).
\end{equation}

\emph{The scaling limit.}  Put $\varepsilon_m=m^{-1/2}u_m$ and
$\eta=m^{-1/2}x_m$, so that $x_m\to x$.  By \eqref{eq:implicit},
\[
m^{-1}u_m\,(u_m+x_m)\,m^{1+\varepsilon_m}
=u_m\,(u_m+x_m)\,m^{\varepsilon_m}
=d\,\kappa\,(1+o(1)),
\]
and since $\varepsilon_m\log m\to0$ (a priori bound above; in the scaling
window $\eta m^{1/2}\to x$), we have $m^{\varepsilon_m}\to1$, hence
\[
u_m\,(u_m+x_m)\longrightarrow d\,\kappa .
\]
Hence every limit point $u$ of $(u_m)$ satisfies $u(u+x)=d\kappa$; the positive
root is $\Phi(x)$, and the negative root is excluded because
$\dimH F_{m,S,B}\ge\frac12$ (Theorem~\ref{thm:multi-residue-asymptotic}(ii)).
Thus $u_m\to\Phi(x)$, which is \eqref{eq:scaling-limit}.
\end{proof}"""

s = rep(s, OLD_PROOF, NEW_PROOF, "step3c")

# ---- subsection intro ------------------------------------------------------
s = rep(
    s,
    "The starting point is the tail equation obtained in the proof of\n"
    "Theorem~\\ref{thm:multi-residue-asymptotic}(iv). We record it in the form needed\n"
    "here, correcting a typographical factor in the displayed formula of that proof\n"
    "(see Remark~\\ref{rem:typo}).",
    "The starting point is the tail equation obtained in the proof of\n"
    "Theorem~\\ref{thm:multi-residue-asymptotic}(iv). We prove the form needed\n"
    "here (Lemma~\\ref{lem:resolvent-uniform} and Lemma~\\ref{lem:master}),\n"
    "correcting a typographical factor in the displayed formula of that proof\n"
    "(see Remark~\\ref{rem:typo}).",
    "intro",
)

# ---- rem:typo references ---------------------------------------------------
s = rep(
    s,
    "\\begin{remark}[Why \\eqref{eq:tail-uniform} has $m^{-1-\\varepsilon}$]\\label{rem:typo}",
    "\\begin{remark}[Why the tail equation has $m^{-1-\\varepsilon}$]\\label{rem:typo}",
    "typo-title",
)
s = rep(
    s,
    "and\n\\eqref{eq:tail-uniform} gives $1\\cdot1\\cdot(m/\\alpha)m^{-1}=1$, i.e.\\ $\\alpha=1$,\n"
    "as it must; the uncorrected display would give $\\alpha=m$.",
    "and\nthe corrected balance gives $1\\cdot1\\cdot(m/\\alpha)m^{-1}=1$, i.e.\\ $\\alpha=1$,\n"
    "as it must; the uncorrected display would give $\\alpha=m$.",
    "typo-body",
)

# ---- supercritical proposition references ---------------------------------
s = rep(
    s,
    "Assume $s_0(S)>\\frac12$, i.e.\\ $\\eta<0$, and assume that\n"
    "\\eqref{eq:tail-uniform} extends to $\\varepsilon$ in a neighbourhood of\n"
    "$\\varepsilon=-\\eta=2s_0-1>0$ with the same $O(m^{-1/2})$ relative error. Then",
    "Assume $s_0(S)>\\frac12$, i.e.\\ $\\eta<0$, and assume that\n"
    "\\eqref{eq:master} extends to $\\varepsilon$ in a neighbourhood of\n"
    "$\\varepsilon=-\\eta=2s_0-1>0$ with the same $O(\\bar\\delta_m)$ error. Then",
    "supercrit-hyp",
)
s = rep(
    s,
    "Substituting into\n\\eqref{eq:tail-uniform} and using $1/\\varepsilon\\to1/(2s_0-1)$ and",
    "Substituting into\n\\eqref{eq:master} and using $1/\\varepsilon\\to1/(2s_0-1)$ and",
    "supercrit-proof",
)
s = rep(
    s,
    "the\nhypothesis that \\eqref{eq:tail-uniform} extends to",
    "the\nhypothesis that \\eqref{eq:master} extends to",
    "supercrit-status",
)

# ---- "What this section proves" bullets ------------------------------------
s = rep(
    s,
    "\\item \\textbf{Proved modulo Hypothesis~\\ref{hyp:tail}.} The joint scaling limit\n"
    "Theorem~\\ref{thm:critical-scaling} and the critical exponent\n"
    "Corollary~\\ref{cor:critical-exp}. Hypothesis~\\ref{hyp:tail} is the statement\n"
    "that the tail equation of Theorem~\\ref{thm:multi-residue-asymptotic}(iv) holds\n"
    "with a relative error $O(m^{-1/2})$ uniformly for $\\varepsilon=O(m^{-1/2+\\delta})$;\n"
    "the existing proof gives it only for $\\varepsilon=O(1/m)$, i.e.\\ strictly inside\n"
    "the subcritical regime. Extending the resolvent estimates to the critical window\n"
    "is the remaining technical step.",
    "\\item \\textbf{Proved.} Lemma~\\ref{lem:resolvent-uniform} and Lemma~\\ref{lem:master}\n"
    "(the uniform resolvent expansion and the master equation, with\n"
    "$K=\\lceil e^{m^3}\\rceil$ on the lower side); hence the joint scaling limit\n"
    "Theorem~\\ref{thm:critical-scaling} and the critical exponent\n"
    "Corollary~\\ref{cor:critical-exp}, both modulo the repo's transfer-operator\n"
    "criterion (Theorem~\\ref{thm:residues-general}(ii), whose step-certificate\n"
    "soundness is kernel-checked as \\texttt{step\\_cert\\_upper\\_sound} and\n"
    "\\texttt{step\\_cert\\_lower\\_sound}).",
    "bullets-proved",
)
s = rep(
    s,
    "(Proposition~\\ref{prop:supercritical-constant}); the uniformity of\n"
    "Hypothesis~\\ref{hyp:tail}; the continuity of $\\kappa(S)$ in $S$; the existence\n"
    "of an integer set $S$ with $s_0(S)=\\frac12$ exactly.",
    "(Proposition~\\ref{prop:supercritical-constant}); the continuity of $\\kappa(S)$ in\n"
    "$S$; the existence of an integer set $S$ with $s_0(S)=\\frac12$ exactly; any\n"
    "Lean formalization of the critical-scaling layer beyond the pole axiom and the\n"
    "scaling-function identity.",
    "bullets-not-proved",
)

SEC.write_text(s, encoding="utf-8")

# ---- Step 4: frontmatter-2C-v3 ---------------------------------------------
f = FM.read_text(encoding="utf-8")
f = rep(
    f,
    "and, conditionally on a uniform tail\nestimate, the critical exponent $1/2$ with amplitude $\\sqrt{d\\kappa(S)}/2$ and\nno log correction.",
    "and the critical exponent $1/2$ with amplitude\n$\\sqrt{d\\kappa(S)}/2$ and no log correction.",
    "fm-abstract",
)
f = rep(
    f,
    "The scaling theorem and the critical exponent are proved only modulo\n"
    "the uniform tail estimate stated as Hypothesis~\\ref{hyp:tail}; that hypothesis\n"
    "is not established here.",
    "The scaling theorem and the critical exponent are proved from the\n"
    "master equation (Lemma \\texttt{lem:master}), whose lower side uses the\n"
    "finite-subalphabet transfer-operator criterion; that criterion's\n"
    "step-certificate soundness is kernel-checked, but the analytic estimates of\n"
    "the critical-scaling section are not Lean-formalized.",
    "fm-honesty",
)
FM.write_text(f, encoding="utf-8")

# ---- Step 5: BUILD_LOG append ----------------------------------------------
log = LOG.read_text(encoding="utf-8")
log += (
    "\n- 2026-11-25 E17：Hypothesis hyp:tail 已升级为 Lemma lem:resolvent-uniform"
    " + lem:master（指挥给出文本，逐字替换）；thm:critical-scaling /"
    " cor:critical-exp 升为定理（modulo 仓库判定准则）。\n"
)
LOG.write_text(log, encoding="utf-8")

# ---- verification -----------------------------------------------------------
bad = [ln for ln in s.splitlines() if "hyp:tail" in ln or "Hypothesis" in ln]
print("E17 done. residual hyp:tail/Hypothesis lines in section:", len(bad))
for ln in bad:
    print("   RESIDUAL:", ln[:100])
ob, cb = s.count("{"), s.count("}")
print(f"braces: {ob}/{cb}  begin/end: "
      f"{s.count(chr(92)+'begin{')}/{s.count(chr(92)+'end{')}")
print("section bytes:", len(s.encode("utf-8")))
