r"""Paper 2 (2026-11-25): correct the description of the Bugeaud--Liao--Rams proof sketch.

rem:poly-BLR and rem:growing-BLR said that the BLR proof sketch "indicates that condition (1.6) may
be removable by an interpolation device of Baker". In arXiv:1710.03596v1 the Baker interpolation is
used for the opposite purpose: it inserts maps when the sequence is too sparse, to secure the lower
bound. Condition (1.6) is invoked directly in both bounds to absorb accumulated distortion errors.
See verification/candidateA_precedent_search_20261125.md section 1. The sentence is replaced by a
neutral statement.

The main tex and the slices that carry the sentence (sec-poly, sec-growing, and the legacy
sec-gauge superset slice) are patched together. The 13 core slices must still concatenate
byte-for-byte to the main file.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper2_spectral_gap_dimension" / "paper2_spectral_gap_dimension.tex"
SL = ROOT / "paper2_spectral_gap_dimension" / "split" / "src_sections"
ORDER = ["sec-preface", "sec-class", "sec-spectrum", "sec-finite", "sec-weights", "sec-gauge-core",
         "sec-finstate", "sec-poly", "sec-growing", "sec-windows", "sec-resasymp", "sec-num",
         "sec-verification"]

OLD = ("(Hypotheses as stated in arXiv:1710.03596v1, whose proof sketch indicates that\n"
       "condition~(1.6) may be removable by an interpolation device of Baker; this is not\n"
       "stated there as a theorem.)")
NEW = ("(Hypotheses as stated in arXiv:1710.03596v1, where the proof of Theorem~7 is\n"
       "given as a sketch.)")


def main():
    rd = lambda p: p.read_bytes().decode("utf-8")
    main_t = rd(TEX)
    core = {n: rd(SL / f"{n}.tex") for n in ORDER}
    assert "".join(core[n] for n in ORDER) == main_t, "slices out of sync before patch"
    assert main_t.count(OLD) == 2
    main_t = main_t.replace(OLD, NEW)
    for n in ("sec-poly", "sec-growing"):
        assert core[n].count(OLD) == 1, n
        core[n] = core[n].replace(OLD, NEW)
    assert "".join(core[n] for n in ORDER) == main_t, "slices out of sync after patch"
    legacy = rd(SL / "sec-gauge.tex")
    assert legacy.count(OLD) == 1
    (SL / "sec-gauge.tex").write_bytes(legacy.replace(OLD, NEW).encode("utf-8"))
    TEX.write_bytes(main_t.encode("utf-8"))
    for n in ("sec-poly", "sec-growing"):
        (SL / f"{n}.tex").write_bytes(core[n].encode("utf-8"))
    print("patched 2 occurrences in main tex, sec-poly, sec-growing, legacy sec-gauge")


if __name__ == "__main__":
    main()
