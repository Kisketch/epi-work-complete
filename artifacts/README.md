<!-- NON-CANONICAL / DO NOT CITE -->
# artifacts/ — 定理单元（THM-xxxx）

Each unit: `statement.md`, `proof.md`, `evaluation.md`, `log.md` (generated from the append-only ledgers, which remain authoritative), `dependencies.md`, and `Lean/` (a byte-identical copy of the library module, or a pointer). Canonical Lean lives in `epi_formal/EpiFormal/`.

| ID | 内容 | 类别 | 状态 | Lean |
|---|---|---|---|---|
| [THM-0001](THM-0001/statement.md) | P1 ⇔ π∉ℚ+ℚe ⇔ {1,e,π} ℚ-线性无关 | 3 | 已核实 | `RationalSpan.lean` |
| [THM-0002](THM-0002/statement.md) | dim_H F_τ = max(1−τ,0)（修补 Paper 1） | 5 | 纸面，双检 | — |
| [THM-0003](THM-0003/statement.md) | L 上的二分（阈值 1/4） | 5 | 已核实 | `Classification.lean`（指针） |
| [THM-0004](THM-0004/statement.md) | BQ_j 的度量 Khintchine 律 | 5 | 纸面，双检（证明在 THM-0003/proof.md） | — |
| [THM-0005](THM-0005/statement.md) | κ = 1/4 尖锐且可达；Paper 2 短文初稿 | 1 的候选 | 已核实 | `KappaSharp.lean` |
| [THM-0006](THM-0006/statement.md) | 一般递推二分（a_j→∞，D≠0） | 5 | 已核实 (A)+(B) | `GeneralDichotomy.lean` |

P1 itself (π ∉ ℚ+ℚe) is OPEN. Nothing here concerns π or e+π.
