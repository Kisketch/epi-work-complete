"""Paper 1 bibliography integrity patch (2026-11-23).

- CambridgeFF: author, volume pages, year, DOI from Crossref (10.1017/cbo9780511735226.004);
  the series number of the volume was not verified and is not added.
- lem:mue: add the primary source Bundschuh, Math. Ann. 192 (1971) 229--242 (Crossref,
  DOI 10.1007/bf02052875); full text not opened, so no theorem number is given.
- Restore citations of the two entries that were defined but never cited (Dan2026,
  BertolinMotives), describing them only by what their titles state.
Each anchor must occur exactly once.
"""
from pathlib import Path

F = Path(__file__).resolve().parent / "paper1_e_plus_pi.tex"

EDITS = [
    (r"\bibitem{CambridgeFF} \emph{Schanuel's conjecture for non-isoconstant elliptic curves over function fields}, Cambridge volume (Model Theory with Applications to Algebra and Analysis).",
     r"\bibitem{CambridgeFF} D.~Bertrand, \emph{Schanuel's conjecture for non-isoconstant elliptic curves over function fields}, in: \emph{Model Theory with Applications to Algebra and Analysis}, Cambridge Univ.~Press, 2008, pp.~41--62, doi:10.1017/cbo9780511735226.004."),
    (r"\begin{lemma}[Classical; Bundschuh, see {\cite{CNU2024}}]\label{lem:mue}",
     r"\begin{lemma}[Classical; Bundschuh {\cite{Bundschuh1971}}, see also {\cite{CNU2024}}]\label{lem:mue}"),
    (r"\bibitem{CambridgeFF}",
     r"\bibitem{Bundschuh1971} P.~Bundschuh, \emph{Irrationalit\"atsma\ss e f\"ur $e^a$, $a\ne0$ rational oder Liouville-Zahl}, Math.~Ann.~192 (1971), 229--242, doi:10.1007/bf02052875." "\n"
     r"\bibitem{CambridgeFF}"),
    (r"is recorded in \cite{Alekseyev2011,FormalConjectures}.",
     r"is recorded in \cite{Alekseyev2011,FormalConjectures}; generalized Flint Hills series are studied in \cite{Dan2026}."),
    (r"Bertolin's preprint \cite{Bertolin2026} (Corollary~\ref{cor:bertolin}) simultaneously extends",
     r"Bertolin's preprint \cite{Bertolin2026} (Corollary~\ref{cor:bertolin}; see also the Schanuel-style conjecture for $1$-motives in \cite{BertolinMotives}) simultaneously extends"),
]


def main():
    t = F.read_text(encoding="utf-8")
    for old, new in EDITS:
        assert t.count(old) == 1, (t.count(old), old[:70])
        t = t.replace(old, new)
    F.write_text(t, encoding="utf-8")
    print("patched", F.name)


if __name__ == "__main__":
    main()
