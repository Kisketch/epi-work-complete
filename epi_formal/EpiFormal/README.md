# epi_formal/EpiFormal/ — Lean 4 模块（146 个顶层模块 + `ResidueCertGen/` 下 200 个）

按模块名前缀分组：

| 分组 | 代表模块 | 内容 |
|---|---|---|
| e 的连分数与基础 | `EulerConvergents`、`Basic`、`Elementary`、`Series`、`Axioms` | 选取分母 Q_j、P_j 的递推与 P_j/Q_j→e；`Axioms.lean` 声明了 `e_transcendental`、`pi_transcendental` 等经典公理（是否被使用以 `#print axioms` 为准） |
| 分类与归约（论文一终点） | `Classification`、`Escape`、`EscapeReduction`、`AdjacentWitness` | L 上的二分（`theorem2_classification`、`corollary3_gap`）；`reduction_to_lattice`；`P1` 的定义 |
| **围攻战役新增** | `RationalSpan`、`KappaSharp`、`GeneralDichotomy` | THM-0001（P1⇔线性无关）、THM-0005（κ=1/4 尖锐可达）、THM-0006（一般二分）；见 [../../artifacts/README.md](../../artifacts/README.md) |
| 窗口与维数 | `Window*`（44 个）、`DimH*`、`Weighted*`、`Cylinder*`、`NoShortDim*` | 窗口计数、质量分布、Hausdorff 维数上下界 |
| 量规、谱与有限状态 | `Gauge*`、`Spectrum`、`SpectralGap`、`FiniteState*`、`FullConvergentSpectrum`、`FullSpectrumDiscrete` | 论文二的谱隙、量规与全收敛谱 |
| 余数证书 | `Residue*`、`ResidueCertGen/`（200 个自动生成模块） | 余数模算术证书与渐近 |
| Padé 与 Meiburg / Alekseyev | `Pade*`、`Meiburg*`、`Alekseyev`、`FlintHills` | Flint Hills 级数方向的条件结果 |
| 其他 | `Golden*`、`Poly*`、`PerronFrobenius`、`MuEEqTwo`、`SupercriticalConstant` 等 | 黄金比轨道、多项式递推、PF 定理、μ(e)=2 |

审计入口（`Audit*.lean`）在上级目录 [../](../README.md)；CI 规则见 [../../.github/workflows/README.md](../../.github/workflows/README.md)。
