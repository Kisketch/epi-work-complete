"""Cross-check (2026-11-24): n=16/24 collocation of asymptotic_residues_check_20261123.py at
m in {4096, 16384}, r in {1,2,3,m}, versus the n=16 values of verify_residue_multi_asymptotic.json.
NON-RIGOROUS numerical evidence (有限计算).  Usage: python asymptotic_largem_crosscheck_20261124.py [workers]
Appends one JSON line per job to asymptotic_largem_crosscheck_20261124.jsonl."""
import json, sys
from multiprocessing import Pool
from pathlib import Path
import asymptotic_residues_check_20261123 as A

HERE = Path(__file__).resolve().parent
OUT = HERE / "asymptotic_largem_crosscheck_20261124.jsonl"

if __name__ == "__main__":
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    jobs = [(m, r if r != "m" else m, float(A.two_term(m, r if r != "m" else m))) for m in (4096, 16384) for r in (1, 2, 3, "m")]
    with Pool(workers) as p:
        for rr in p.imap_unordered(A.job, jobs):
            with open(OUT, "a") as fh:
                fh.write(json.dumps(rr) + "\n")
            print(json.dumps(rr), flush=True)
