"""Fit per-level decay rates of the normalized Fourier energy D_n(h) (Lemma D probe) and compare
with the diagonal rate 1/(2 eps v). Reads verification/kahane_lemmaD_fourier_20261125.json.
Least squares of log D_n(h) on n over the second half of the levels. Evidence only."""
import json, math
d = json.load(open("verification/kahane_lemmaD_fourier_20261125.json"))
for label, r in d.items():
    v, eps = r["v"], r["eps"]
    rows = r["rows"][len(r["rows"]) // 2:]
    out = []
    for h in range(3):
        xs = [row["n"] for row in rows]; ys = [math.log(row["D"][h]) for row in rows]
        mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
        out.append(math.exp(slope))
    print(f"{label:24s} fitted per-level ratio D_(n+1)/D_n: h=1 {out[0]:.3f}, h=2 {out[1]:.3f}, h=3 {out[2]:.3f}"
          f" | diagonal rate 1/(2 eps v) = {1/(2*eps*v):.3f}")
