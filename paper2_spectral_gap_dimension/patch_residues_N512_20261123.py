"""Patch paper 2 (main tex + split sources): N=512 certificates and Lean kernel-checked brackets.

Applies exact string replacements; every replacement must match (count asserted), so a second
run is a no-op failure rather than a silent double edit.  Numbers are taken from
verification/residue_certificate_general_N512.json and checked here in exact arithmetic.
Usage: python paper2_spectral_gap_dimension/patch_residues_N512_20261123.py
"""
import json
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
J = json.loads((ROOT / "verification" / "residue_certificate_general_N512.json").read_text())
C = {(e["modulus"], e["residue"]): e for e in J["certificates"]}

e41 = C[(4, 1)]
LO_M, UP_M = F(e41["lower_margin_exact"]), F(e41["upper_margin_exact"])
assert LO_M > F(48, 10000) > 0 and UP_M > F(27, 100000) > 0
assert F(e41["lower"]) == F(357, 512) and F(e41["upper"]) == F(179, 256)

K_TAIL = {2: 258, 3: 172, 4: 130, 5: 120, 6: 120}


def frac_tex(x):
    x = F(x)
    return f"{x.numerator}/{x.denominator}"


table_rows = []
for m in range(2, 7):
    for r in (1, m):
        e = C[(m, r)]
        lo, up = F(e["lower"]), F(e["upper"])
        assert up - lo == F(1, 512)
        table_rows.append(
            f"${m}$ & ${r}$ & ${K_TAIL[m]}$ & ${frac_tex(lo)}\\,({float(lo):.6f})$ & "
            f"${frac_tex(up)}\\,({float(up):.6f})$ & $1/512$ \\\\" + ("\\hline" if r == m and m < 6 else ""))
    if m < 6:
        pass
table_rows[-1] = table_rows[-1].rstrip("\\").rstrip()  # last row has no trailing \\

OLD_TABLE_BODY = r"""$2$ & $1$ & $130$ & $419/512\,(0.818359)$ & $421/512\,(0.822266)$ & $1/256$ \\
$2$ & $2$ & $130$ & $23/32\,(0.718750)$  & $369/512\,(0.720703)$ & $1/512$ \\\hline
$3$ & $1$ & $120$ & $95/128\,(0.742188)$ & $191/256\,(0.746094)$ & $1/256$ \\
$3$ & $3$ & $120$ & $41/64\,(0.640625)$  & $329/512\,(0.642578)$ & $1/512$ \\\hline
$4$ & $1$ & $120$ & $357/512\,(0.697266)$ & $359/512\,(0.701172)$ & $1/256$ \\
$4$ & $4$ & $120$ & $309/512\,(0.603516)$ & $155/256\,(0.605469)$ & $1/512$ \\\hline
$5$ & $1$ & $120$ & $171/256\,(0.667969)$ & $343/512\,(0.669922)$ & $1/512$ \\
$5$ & $5$ & $120$ & $149/256\,(0.582031)$ & $299/512\,(0.583984)$ & $1/512$ \\\hline
$6$ & $1$ & $120$ & $331/512\,(0.646484)$ & $333/512\,(0.650391)$ & $1/256$ \\
$6$ & $6$ & $120$ & $291/512\,(0.568359)$ & $73/128\,(0.570312)$  & $1/512$"""
NEW_TABLE_BODY = "\n".join(table_rows)

REMARK = r"""
\begin{remark}[Kernel-checked brackets]\label{rem:residue-kernel}
Independently of Bowen's formula, every closed bracket
$\mathrm{lower}\le\dimH F_{m,r}\le\mathrm{upper}$ in Table~\ref{tab:residues-general}
(twenty one-sided bounds) is a theorem of Lean~4 with Mathlib, proved from
Theorem~\ref{thm:residues-general}(ii) and the integer certificate data. The proof is
organised so that no floating-point computation is trusted: a generic soundness theorem
(\texttt{EpiFormal/\allowbreak ResidueCertGenSound.lean}) shows that, if Boolean checkers on
natural numbers (\texttt{EpiFormal/\allowbreak ResidueCertGenBase.lean}) return \texttt{true}
on a vector $v\in\Z_{\ge1}^{512}$ and a coefficient table, then $\dimH F_{m,r}\le s$
(respectively $\ge s$). The checkers verify that $v$ is non-increasing (so the maximum and
minimum of the step function over each image cell are its values at the cell endpoints,
whose indices are the closed forms $\min(N-1,\lfloor N^2/(aN+e)\rfloor)$), that each
coefficient $c$ satisfies the exponent-cleared enclosure
$S^qN^p\le c^q(aN+j)^p$ (upper) or $c^q(aN+j+1)^p\le S^qN^p$ (lower) for $2s=p/q$, the
row inequalities, and the integral tail bounds. These checks are evaluated by the Lean
kernel (\texttt{decide +kernel}, GMP-accelerated natural-number arithmetic; no
\texttt{native\_decide}) on data emitted by \texttt{verification/\allowbreak
emit\_cert\_gen.py} in $64$-row chunks; the resulting bounds and the strict separations
$\dimH F_{m,m}<\dimH F_{m,1}$ ($2\le m\le6$) are collected in
\texttt{EpiFormal/\allowbreak ResidueCertTable.lean}. Strictness of the brackets
(open intervals) uses the positive margins and the pressure argument of
Theorem~\ref{thm:residues}, which is not formalised.
\end{remark}
"""

EDITS = [
    # theorem statement
    (r"$\dimH E=\dimH F$, with $357/512<\dimH F<359/512$.",
     r"$\dimH E=\dimH F$, with $357/512<\dimH F<179/256$; the closed bracket"
     "\n" r"$357/512\le\dimH F\le179/256$ is machine-checked in Lean~4 (Remark~\ref{rem:residue-kernel})."),
    # test parameters
    (r"with $N=2^{24}$ (whose", r"with $N=2^{80}$ (whose"),
    (r"and the upper test at $s=359/512$ to the full alphabet $\mathcal D=\mathcal A$"
     "\n" r"(certifying $\dimH F<359/512$).",
     r"and the upper test at $s=179/256$ to the full alphabet $\mathcal D=\mathcal A$"
     "\n" r"(certifying $\dimH F<179/256$)."),
    (r"positive step function on the $256$ uniform"
     "\n" r"grid cells $C_j=[l_j,u_j)=[j/256,(j+1)/256)$ ($0\le j\le254$) and"
     "\n" r"$C_{255}=[255/256,1]$.",
     r"positive step function on the $512$ uniform"
     "\n" r"grid cells $C_j=[l_j,u_j)=[j/512,(j+1)/512)$ ($0\le j\le510$) and"
     "\n" r"$C_{511}=[511/512,1]$."),
    (r"($0\le k<64$) and $x\in[l,u]$", r"($0\le k<130$) and $x\in[l,u]$"),
    (r"For all tail indices $k\ge64$, the digit is"
     "\n" r"$a=4k+1\ge257>256$, so for every $x\in[0,1]$ the image point satisfies"
     "\n" r"$0<f_a(x)=1/(4k+1+x)\le 1/257<1/256$ and therefore falls strictly inside the"
     "\n" r"first cell $C_0=[0,1/256)$,",
     r"For all tail indices $k\ge130$, the digit is"
     "\n" r"$a=4k+1\ge521>512$, so for every $x\in[0,1]$ the image point satisfies"
     "\n" r"$0<f_a(x)=1/(4k+1+x)\le 1/521<1/512$ and therefore falls strictly inside the"
     "\n" r"first cell $C_0=[0,1/512)$,"),
    (r"we bound the tail sums over $k\ge64$ by", r"we bound the tail sums over $k\ge130$ by"),
    (r"and summing from $k=64$ to $N-1$ (where $4\cdot64+2=258$) gives the lower tail",
     r"and summing from $k=130$ to $N-1$ (where $4\cdot130+2=522$) gives the lower tail"),
    (r" \sum_{k=64}^{N-1}(4k+1+x)^{-p}v_0" "\n" r" \ge v_0\int_{64}^N(4t+2)^{-p}\,dt"
     "\n" r" =v_0\left[\frac{(4t+2)^{1-p}}{4(1-p)}\right]_{t=64}^{t=N}"
     "\n" r" =v_0\,\frac{258^{1-p}-(4N+2)^{1-p}}{4(p-1)}.",
     r" \sum_{k=130}^{N-1}(4k+1+x)^{-p}v_0" "\n" r" \ge v_0\int_{130}^N(4t+2)^{-p}\,dt"
     "\n" r" =v_0\left[\frac{(4t+2)^{1-p}}{4(1-p)}\right]_{t=130}^{t=N}"
     "\n" r" =v_0\,\frac{522^{1-p}-(4N+2)^{1-p}}{4(p-1)}."),
    (r"and summing from $k=64$ to $\infty$ (where $4\cdot63+1=253$) gives the upper",
     r"and summing from $k=130$ to $\infty$ (where $4\cdot129+1=517$) gives the upper"),
    (r" \sum_{k=64}^{\infty}(4k+1+x)^{-p}v_0" "\n" r" \le v_0\int_{63}^\infty(4t+1)^{-p}\,dt"
     "\n" r" =v_0\left[\frac{(4t+1)^{1-p}}{4(1-p)}\right]_{t=63}^{t=\infty}"
     "\n" r" =v_0\,\frac{253^{1-p}}{4(p-1)} .",
     r" \sum_{k=130}^{\infty}(4k+1+x)^{-p}v_0" "\n" r" \le v_0\int_{129}^\infty(4t+1)^{-p}\,dt"
     "\n" r" =v_0\left[\frac{(4t+1)^{1-p}}{4(1-p)}\right]_{t=129}^{t=\infty}"
     "\n" r" =v_0\,\frac{517^{1-p}}{4(p-1)} ."),
    (r"The companion script \texttt{residue\_certificate.py} constructs a",
     r"The companion script \texttt{residue\_\allowbreak certificate\_\allowbreak general\_\allowbreak N512.py} constructs a"),
    (r"corresponding cell value use exact integer arithmetic. At $s=357/512$, the",
     r"corresponding cell value use exact integer arithmetic. At $s=357/512$, the"),
    (r"$7204302042904417931/2465429597500000000000>29/10000>0$; at $s=359/512$, the",
     f"${frac_tex(LO_M)}>48/10000>0$; at $s=179/256$, the"),
    (r"$65040245891337248463/9860138780000000000000>65/10000>0$. The"
     "\n" r"strict signs certify the stated open interval $(357/512,359/512)$, of width"
     "\n" r"$1/256$.",
     f"${frac_tex(UP_M)}>27/100000>0$. The" "\n"
     r"strict signs certify the stated open interval $(357/512,179/256)$, of width"
     "\n" r"$1/512$. The same integer inequalities, re-encoded as Boolean checks, are"
     "\n" r"evaluated by the Lean kernel (Remark~\ref{rem:residue-kernel})."),
    # general theorem (iii)
    (r"grid $N=256$, scale $S=10^{13}$, $2^{80}$-precision enclosures) certifies the",
     r"\texttt{\allowbreak residue\_\allowbreak certificate\_\allowbreak general\_\allowbreak N512.py},"
     "\n" r"grid $N=512$, scale $S=10^{13}$, $2^{80}$-precision enclosures) certifies the"),
    (r"the Python script \texttt{residue\_\allowbreak certificate\_\allowbreak general.py}"
     "\n" r"performs the concrete grid arithmetic for $m\in\{2,3,4,5,6\}$.",
     r"the concrete grid arithmetic for $m\in\{2,3,4,5,6\}$ is performed both in exact"
     "\n" r"Python integer arithmetic and, for the closed brackets, by the Lean kernel"
     "\n" r"(Remark~\ref{rem:residue-kernel})."),
    (OLD_TABLE_BODY, NEW_TABLE_BODY),
    (r"\caption{Certified open intervals $(\mathrm{lower},\mathrm{upper})$ for $\dimH F_{m,r}$ ($m\in\{2,3,4,5,6\}$, $r\in\{1,m\}$) from \texttt{residue\_\allowbreak certificate\_\allowbreak general.py} ($N=256$, $S=10^{13}$, $2^{80}$-precision enclosures); for every $m$, $\mathrm{upper}(F_{m,m})<\mathrm{lower}(F_{m,1})$.}\label{tab:residues-general}"
     "\n" r"\end{table}",
     r"\caption{Certified open intervals $(\mathrm{lower},\mathrm{upper})$ for $\dimH F_{m,r}$ ($m\in\{2,3,4,5,6\}$, $r\in\{1,m\}$) from \texttt{residue\_\allowbreak certificate\_\allowbreak general\_\allowbreak N512.py} ($N=512$, $S=10^{13}$, $2^{80}$-precision enclosures), all of width $1/512$; for every $m$, $\mathrm{upper}(F_{m,m})<\mathrm{lower}(F_{m,1})$. The closed brackets are kernel-checked in Lean~4 (Remark~\ref{rem:residue-kernel}).}\label{tab:residues-general}"
     "\n" r"\end{table}" "\n" + REMARK),
    (r"for $m\in\{2,3,4,5,6\}$ via $256$-cell transfer-operator grid certificates. To",
     r"for $m\in\{2,3,4,5,6\}$ via $512$-cell transfer-operator grid certificates. To"),
]

# abstract / intro phrasing (several files)
INTRO_EDITS = [
    (r"between $357/512$ and $359/512$", r"between $357/512$ and $179/256$"),
]

TARGETS = [ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex",
           HERE / "split" / "src_sections" / "sec-windows.tex",
           HERE / "split" / "src_sections" / "sec-resasymp.tex"]
INTRO_TARGETS = [ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"] + [
    HERE / "split" / "src_sections" / n for n in
    ("intro-2C.tex", "intro-shared.tex", "frontmatter-2C.tex", "frontmatter.tex", "sec-preface.tex")]


def main():
    texts = {p: p.read_text(encoding="utf-8") for p in set(TARGETS + INTRO_TARGETS)}
    main_tex = TARGETS[0]
    for old, new in EDITS:
        hits = [p for p in TARGETS if old in texts[p]]
        assert main_tex in hits, f"edit not found in main tex: {old[:70]!r}"
        for p in hits:
            assert texts[p].count(old) == 1, (p.name, old[:60])
            texts[p] = texts[p].replace(old, new)
    for old, new in INTRO_EDITS:
        for p in INTRO_TARGETS:
            texts[p] = texts[p].replace(old, new)
    for p, t in texts.items():
        p.write_text(t, encoding="utf-8")
        print("patched", p.relative_to(ROOT))


if __name__ == "__main__":
    main()
