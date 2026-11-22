$ErrorActionPreference='Stop'
$path='第一阶段_e_plus_pi.tex'
$src=[System.IO.File]::ReadAllLines((Join-Path (Get-Location) $path))
function Seg([int]$a,[int]$b){ $src[($a-1)..($b-1)] }

$A=@'
\subsection{Technical baseline: two classical irrationality proofs}

\begin{theorem}[Fourier]\label{thm:fourier}
$\ee$ is irrational.
\end{theorem}

\begin{theorem}[Niven]\label{thm:niven}
$\pi$ is irrational.
\end{theorem}

Both statements are weaker than the Hermite--Lindemann theorem
(Theorem~\ref{thm:HL}) and are recorded only as a technical
baseline. Fourier's proof for $\ee$ multiplies the truncated
exponential series by $n!$: the main term clears denominators and
is an integer, while the tail
$I_n=n!\bigl(\ee-\sum_{k\le n}1/k!\bigr)$ satisfies $0<I_n<1/n$.
Niven's proof for $\pi$ integrates $f(x)=x^n(a-bx)^n/n!$ against
$\sin x$ over $[0,\pi]$; every even derivative at the endpoints is
integral, and the integral is a positive integer tending to $0$,
hence eventually lies strictly in $(0,1)$. Both proofs construct a
quantity that is an integer under the rationality hypothesis and
independently lies strictly in $(0,1)$. Three ingredients are
required: (i) a rapidly convergent series or integral
representation; (ii) a ``denominator-clearing'' mechanism making
the main term integral; (iii) separation of main term and tail
with controlled error. The obstruction analysis of
\S\ref{sec:obstructions} shows that each attempted route to
$e+\pi$ fails at ingredient (ii) or (iii), at an identifiable
structural point. Expository accounts of both proofs are given in
\cite{Conrad}.
'@

$B=@'
\section{Window periods and the converse to denominator locking}\label{sec:windows}

This chapter establishes the periodic window structure that
rationality forces on the continued fraction of $e+x$.
Theorem~\ref{thm:explicit-period} gives an explicit necessary
period under rationality. Theorem~\ref{thm:digit-shift} gives the
complete digit change and forces eventual periodicity modulo four
in ordinary digit indices. Corollary~\ref{cor:digit-statistics}
gives tests in terms of the growth of ordinary convergent
denominators and the multiplicities of large digit values.
Theorem~\ref{thm:gcd-converse} identifies unboundedness of either
denominator quotient for $\pi$ with rational linear independence
of $1,e,\pi$. Corollary~\ref{cor:recover-slope} isolates the slope
needed for the sum. Whether the actual $\pi$ violates the slope
condition remains unresolved.
'@

$B2=@'
\subsection{Denominator restrictions at the Dirichlet scale}\label{sec:current-results}
'@

$B3=@'
\subsection{Two primitive witnesses, signed forms, and a series obstruction}
'@

$C=@'
\section{The bounded golden-orbit limit spectrum}\label{sec:golden}

This chapter evaluates, by a finite exact algorithm, the bounded
golden-ratio orbit limit spectrum for every reduced rational
affine image of $e$, and establishes the complete Case~1 and
Case~2 classifications of the exact constants $c_\varphi$, all
extremal families, and the second smallest limit points.
'@

$D=@'
\section{General quadratic orbits, ideal classes, and uniform interval counting}\label{sec:quadratic}

This chapter extends the finite-spectrum analysis from the golden
ratio to arbitrary real quadratic orbits, factors the trace test
through invertible ideal classes, and counts the finite limits
uniformly over admissible intervals.
'@

$E=@'
\section{Reductions, obstructions, and conditional frameworks}\label{sec:new}

This chapter assembles the material directed at
Problem~\ref{prob:main} itself: the elementary reductions and
conditional implications, the systematic obstruction analysis, the
conditional frameworks, and the exclusion map with the surviving
targets. The material is diagnostic: the verdicts concern specific
constructions; they are not meta-theorems that no proof along the
general line can exist.
'@

$E2=@'
\subsection*{Systematic attempts and obstruction analysis}\label{sec:obstructions}
'@

$E3=@'
\subsection*{Conditional frameworks and the frontier}\label{sec:conditional}
'@

$F=@'
\section{Conclusion and open problems}\label{sec:conclusion}

This section records what the assembled results decide, the
companion metric context, and the research priorities. Whether the
actual $\pi$ violates the slope condition of
Corollary~\ref{cor:recover-slope} remains unresolved.
'@

$F2=@'
\paragraph{Companion metric results.} The revised companion
\cite{CompanionGauge} gives dimension $1-\alpha$ for prescribed
admissible limits of $j^\alpha\|Q_jx\|$ when $0\le\alpha<1$ and an
exact Hausdorff gauge for each positive critical spectral level;
both have paper proofs. In particular the unweighted zero-set has
dimension one, whereas the weighted zero-set at exponent one
equals the countable group $L$. The counterexample to their
equality was separately kernel-checked in
\texttt{UnweightedCorrection.lean}. Neither dimension calculation
decides membership for the prescribed point $\pi$.
'@

$G=@'
\section*{Use of AI and formal verification}
This work was carried out with substantial assistance from
generative AI systems (including ChatGPT and Codex), both for
developing and drafting mathematical arguments and text,
preparing the numerical certificates, and writing the Lean~4
formalization. The results marked as kernel-checked were verified
by the Lean~4 kernel, and their axiom dependencies were audited
with \texttt{\#print axioms} (349 audited declarations; 327
depend only on the Lean base axioms \texttt{propext},
\texttt{Classical.choice}, and \texttt{Quot.sound}, and 22 use the
registered transcendence/irrationality-measure whitelist axioms
\texttt{e\_transcendental}, \texttt{pi\_transcendental}, and
\texttt{mu\_e\_eq\_two}; zero \texttt{sorryAx}). The remaining
paper proofs---including the window and spectrum computations of
Sections~\ref{sec:windows}--\ref{sec:quadratic} and the obstruction
analysis---are not machine-checked; they have been checked by
line-by-line re-derivation within the same AI-assisted workflow
and cross-checked against the reproducible scripts and Lean
audits of Appendices~\ref{sec:computation}--\ref{app:repro}; they
have not yet been examined by an independent human referee.
'@

function L([string]$s){ ($s -split "`n" | ForEach-Object { $_.TrimEnd("`r") }) }

$out=@()
$out+=Seg 1 123        # preamble + Introduction
$out+=Seg 124 168      # Preliminaries
$out+=Seg 170 234      # unconditional results 3.1-3.3 (subsection level)
$out+=(L $A)           # compressed Fourier/Niven baseline
$out+=Seg 296 298      # stronger known results
$out+=(L $B)           # new Sec 3 header + lead
$out+=(L $B2)          # retitled 8.1 header
$out+=Seg 790 828      # 8.1 body (dirichlet-divisor)
$out+=(L $B3)          # retitled 8.2 header
$out+=Seg 842 936      # 8.2 body (two-window, signed-round, Machin)
$out+=Seg 937 1118     # 8.3 explicit period
$out+=Seg 1119 1208    # 8.4 gcd-converse
$out+=Seg 1209 1441    # 8.5 affine-window
$out+=(L $C)           # new Sec 4 header
$out+=Seg 1442 2557    # 8.6 golden orbit
$out+=(L $D)           # new Sec 5 header
$out+=Seg 2558 3377    # 8.7-8.8 general quadratic
$out+=Seg 3530 3924    # 8.12 ideal classes
$out+=(L $E)           # new Sec 6 header + lead
$out+=Seg 301 609      # former Sec 4 (reductions), header dropped
$out+=(L $E2)          # group header: obstructions
$out+=Seg 611 669      # former Sec 5 (routes), header dropped
$out+=(L $E3)          # group header: conditional
$out+=Seg 671 709      # former Sec 6 (conditional), header dropped
$out+=Seg 3378 3529    # 8.9-8.11 exclusion/surviving/adaptive
$out+=(L $F)          # new Sec 7 conclusion header + lead
$out+=(L $F2)          # companion metric paragraph (rewritten)
$out+=Seg 3925 3953    # 8.13 research priorities
$out+=(L $G)           # Use of AI
$out+=Seg 4454 4529    # bibliography
$out+=Seg 4530 4533    # clearpage + appendix
$out+=Seg 710 785      # computation -> Appendix A
$out+=Seg 3954 4453    # Lean -> Appendix B
$out+=Seg 4534 4566    # audit -> Appendix C
$out+=Seg 4567 4592    # reproducibility -> Appendix D
$out+=Seg 4593 4596    # end

$out = $out | Where-Object { $true }
$dest=Join-Path (Get-Location) '_restructured_tmp.tex'
[System.IO.File]::WriteAllLines($dest, $out, (New-Object System.Text.UTF8Encoding($false)))
Write-Output ("total lines: " + $out.Count)
Write-Output "sections in order:"
$out | Select-String -Pattern '^\\(section|appendix)\b' | ForEach-Object { $_.Line }
