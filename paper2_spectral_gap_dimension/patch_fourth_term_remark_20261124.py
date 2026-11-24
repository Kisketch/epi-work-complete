r"""Paper 2 (2026-11-24): heuristic fourth-order term remark + second independent rebuild status.

1. Inserts Remark rem:fourth-term (with Table tab:fourth-term) right after
   Table tab:multi-residue-asymptotic.  Every number is computed here from the archived data via
   verification/fourth_term_fit_20261124.py (no hand-typed values).  Classification: heuristic
   conjecture with non-rigorous numerical evidence (有限计算 / 数值佐证); it is NOT a theorem.
2. Updates the formal-verification paragraph: ResidueMultiAsymptotic was rebuilt and re-audited on
   a second machine (verification/colab_rebuild_audit_20261124.md).
The same replacements are applied to the split slices, and the byte-exact concatenation of the
13 slices is asserted to equal the patched main file.
"""
import hashlib
import json
import sys
from pathlib import Path

from mpmath import mpf, log

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification"))
import fourth_term_fit_20261124 as F  # noqa: E402

TEX = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"
SL = ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections"
ORDER = ["sec-preface", "sec-class", "sec-spectrum", "sec-finite", "sec-weights", "sec-gauge-core",
         "sec-finstate", "sec-poly", "sec-growing", "sec-windows", "sec-resasymp", "sec-num",
         "sec-verification"]
CROSS = ROOT / "verification" / "asymptotic_largem_crosscheck_20261124.jsonl"

ROWS = [("r=1", r"$\{1\}$", r"$\emptyset$"), ("r=2", r"$\{2\}$", r"$\emptyset$"),
        ("r=3", r"$\{3\}$", r"$\emptyset$"), ("r=m (B={0})", r"$\emptyset$", r"$\{0\}$"),
        ("S={}, B={0,1}", r"$\emptyset$", r"$\{0,1\}$"), ("S={1}, B={0}", r"$\{1\}$", r"$\{0\}$"),
        ("S={2,3}, B={}", r"$\{2,3\}$", r"$\emptyset$"), ("S={1,4}, B={}", r"$\{1,4\}$", r"$\emptyset$"),
        ("S={2,4,5}, B={}", r"$\{2,4,5\}$", r"$\emptyset$"), ("S={1,3}, B={}", r"$\{1,3\}$", r"$\emptyset$")]
MS = (1024, 4096, 16384)


def fmt(x):
    x = float(x)
    if abs(x) >= 100:
        return f"${x:+.0f}$"
    if abs(x) >= 10:
        return f"${x:+.1f}$"
    return f"${x:+.3f}$"


def table_and_facts():
    cases = F.load()
    lines, decreasing_all, decreasing_late, increasing = [], [], [], []
    for label, S, B in ROWS:
        C, Cp, pts = cases[label]
        vals = [(pts[m][0] - F.model_dim(m, C, Cp)) * mpf(m) ** 3 / log(m) ** 2 for m in MS]
        pred = mpf(3) / 4 * C ** 3
        a = [abs(v) for v in vals]
        if a[0] > a[1] > a[2]:
            decreasing_all.append(label)
        elif a[1] > a[2]:
            decreasing_late.append(label)
        else:
            increasing.append(label)
        g = float(C)
        lines.append(f"{S} & {B} & ${g:.4g}$ & " + " & ".join(fmt(v) for v in vals) + f" & {fmt(pred)} \\\\")
    return lines, decreasing_all, decreasing_late, increasing, cases


def crosscheck(cases):
    recs = [json.loads(l) for l in CROSS.read_text().splitlines() if l.strip()]
    assert len(recs) == 8, ("cross-check incomplete", len(recs))
    worst, worst_n = mpf(0), 0.0
    for d in recs:
        label = "r=m (B={0})" if d["r"] == d["m"] else f"r={d['r']}"
        other = cases[label][2][d["m"]][0]
        worst = max(worst, abs(mpf(d["dim_n26"]) - other))
        worst_n = max(worst_n, d["n_diff"])
    return worst, worst_n


def upper_pow10(x):
    """Smallest integer k with |x| < 10^k (for 'less than 10^k' statements)."""
    k = int(f"{float(x):.0e}".split("e")[1]) + 1
    assert abs(float(x)) < 10.0 ** k
    return k


def main():
    rows, dec_all, dec_late, inc, cases = table_and_facts()
    worst, worst_n = crosscheck(cases)
    worst_exp, n_exp = upper_pow10(worst), upper_pow10(worst_n)
    n1024 = max(json.loads(l)["n_diff"] for l in
                (ROOT / "verification" / "asymptotic_residues_check_20261123.partial.jsonl").read_text().splitlines()
                if json.loads(l)["m"] == 1024)
    # contribution of the cross-check discrepancy to the normalized quantity at m=16384
    contrib = float(worst * mpf(16384) ** 3 / log(16384) ** 2)
    assert inc == ["S={1,3}, B={}"], inc
    assert len(dec_all) == 7 and len(dec_late) == 2, (dec_all, dec_late)
    remark = r"""
\begin{remark}[A heuristic fourth-order term; not proved]\label{rem:fourth-term}
Put $\Gamma:=d\,C_S$, $\Gamma':=d\,C_S'$ and $\varepsilon:=2\dimH F_{m,S,B}-1$. Replacing the
leading eigenvalue of the transfer operator by its scalar part and $\zeta(1+\varepsilon)$ by
$\varepsilon^{-1}+\gamma$ (part~(iii)) leads to the scalar model
\[
\varepsilon\,m=(\Gamma-\varepsilon\Gamma')(1+\gamma\varepsilon)\,m^{-\varepsilon},
\]
whose small root we denote by $\varepsilon_m^{\mathrm{mod}}$. Expanding it (symbolically, with
\texttt{sympy}) gives
\[
\frac{1+\varepsilon_m^{\mathrm{mod}}}{2}=\frac12+\frac{\Gamma}{2m}-\frac{\Gamma^2\log m}{2m^2}
+\frac{\Gamma(\gamma\Gamma-\Gamma')}{2m^2}+\frac{3\Gamma^3(\log m)^2}{4m^3}
+O\Bigl(\frac{\log m}{m^3}\Bigr),
\]
whose first four terms are exactly those proved in~\eqref{eq:multi-dimH-three-term}. This
suggests, \emph{as a conjecture}, that in the subcritical regime
\[
\dimH F_{m,S,B}=\frac12+\frac{\Gamma}{2m}-\frac{\Gamma^2\log m}{2m^2}
+\frac{\Gamma(\gamma\Gamma-\Gamma')}{2m^2}+\frac{3\Gamma^3(\log m)^2}{4m^3}
+O\Bigl(\frac{\log m}{m^3}\Bigr).
\]
Table~\ref{tab:fourth-term} compares the model directly with collocation values of the
dimension; this comparison does not depend on fitting the $\log m/m^3$ and $1/m^3$ terms, which a
free least-squares fit cannot separate from the $(\log m)^2/m^3$ term for $\log m\le 10$. If the
conjecture holds, the tabulated quantity tends to $0$, whereas if the coefficient
$\frac34\Gamma^3$ were wrong it would tend to a nonzero constant. In """ + str(len(dec_all)) + r""" of the ten
cases its absolute value decreases over $m=1024,4096,16384$; in """ + str(len(dec_late)) + r""" more it
decreases from $m=4096$ to $m=16384$; for $S=\{1,3\}$ ($\Gamma\approx40.9$) it still increases,
i.e.\ $m\le16384$ is not yet in the asymptotic range for this case. The values for $m=1024$
and $r\in\{1,2,3,m\}$ come from \texttt{verification/\allowbreak asymptotic\_\allowbreak residues\_\allowbreak check\_\allowbreak 20261123.py}
(collocation sizes $16$ and $24$, which differ there by less than $10^{""" + str(upper_pow10(n1024)) + r"""}$); the others from
\texttt{verify\_\allowbreak residue\_\allowbreak multi\_\allowbreak asymptotic.py}. For $m\in\{4096,16384\}$ and
$r\in\{1,2,3,m\}$ the first script reproduces the second to within $10^{""" + str(worst_exp) + r"""}$
(changing the tabulated quantity by less than $10^{""" + str(upper_pow10(contrib)) + r"""}$), with
collocation sizes differing by less than $10^{""" + str(n_exp) + r"""}$. All of this is non-rigorous numerical
evidence (\texttt{verification/\allowbreak fourth\_\allowbreak term\_\allowbreak fit\_\allowbreak 20261124.py}); neither the
fourth term nor the size of the remainder is proved.
\end{remark}

\begin{table}[ht]
\centering\small\setlength{\tabcolsep}{4pt}
\begin{tabular}{c|c|c|ccc|c}
$S$ & $B$ & $\Gamma=dC_S$ & $m=1024$ & $m=4096$ & $m=16384$ & $\frac34\Gamma^3$ \\\hline
""" + "\n".join(rows) + r"""
\end{tabular}
\caption{The quantity $m^3\bigl(\dimH F_{m,S,B}-\frac{1+\varepsilon_m^{\mathrm{mod}}}{2}\bigr)/(\log m)^2$
of Remark~\ref{rem:fourth-term} (non-rigorous collocation values). The last column is the
coefficient of $(\log m)^2/m^3$ in the model, for scale: the tabulated quantity would tend to a
nonzero constant if this coefficient were wrong.}\label{tab:fourth-term}
\end{table}
"""
    anchor = "\\label{tab:multi-residue-asymptotic}\n\\end{table}\n"
    old_ver = (r"while \texttt{ResidueMultiAsymptotic.lean} and \texttt{AuditResidueMultiAsymptotic.lean} were "
               r"built and audited locally on the same Lean~4.35.0 / Mathlib v4.35.0 toolchain.")
    new_ver = (r"and on 2026-11-24 a second clean-clone rebuild on a separate machine (commit \texttt{d920a81}, "
               r"which contains \texttt{ResidueMultiAsymptotic.lean}) reproduced the $937$ main entries, the $27$ "
               r"residue-certificate entries and the $24$ entries of \texttt{AuditResidueMultiAsymptotic.lean} "
               r"entry by entry, all $27+24$ on the three base axioms only "
               r"(\texttt{verification/\allowbreak colab\_\allowbreak rebuild\_\allowbreak audit\_\allowbreak 20261124.md}).")

    def patch(text, need_anchor, need_ver):
        assert "rem:fourth-term" not in text
        if need_anchor:
            assert text.count(anchor) == 1
            text = text.replace(anchor, anchor + remark)
        if need_ver:
            assert text.count(old_ver) == 1
            text = text.replace(old_ver, new_ver)
        return text

    main_t = TEX.read_bytes().decode("utf-8")
    slices = {n: (SL / f"{n}.tex").read_bytes().decode("utf-8") for n in ORDER}
    assert "".join(slices[n] for n in ORDER) == main_t, "slices out of sync before patch"
    main_t = patch(main_t, True, True)
    slices["sec-resasymp"] = patch(slices["sec-resasymp"], True, False)
    slices["sec-verification"] = patch(slices["sec-verification"], False, True)
    assert "".join(slices[n] for n in ORDER) == main_t, "slices out of sync after patch"
    TEX.write_bytes(main_t.encode("utf-8"))
    for n in ("sec-resasymp", "sec-verification"):
        (SL / f"{n}.tex").write_bytes(slices[n].encode("utf-8"))
    print("patched; sha256", hashlib.sha256(main_t.encode("utf-8")).hexdigest(),
          "| decreasing(all):", dec_all, "| decreasing(late):", dec_late, "| increasing:", inc,
          "| cross-check max diff", float(worst), "max n_diff", worst_n, "contrib", contrib)


if __name__ == "__main__":
    main()
