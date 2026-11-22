# Git 目录表（epi_formal 工程）

拷贝时带入的 `.git` 元数据已按去指纹要求移除（其 config/提交历史可能含真实身份）。
本表列出工程的 git 相关目录与受版本控制的内容，便于在 guest 内重新 `git init` 管理。

## 一、git 相关目录/文件（现存）

| 路径 | 类型 | 说明 |
|------|------|------|
| epi_formal/.gitignore | 文件 | 忽略规则（.lake 等） |
| epi_formal/.github/workflows/lean_action_ci.yml | 文件 | Lean CI 工作流 |
| epi_formal/.github/workflows/create-release.yml | 文件 | 发布工作流 |
| epi_formal/.github/workflows/update.yml | 文件 | 依赖更新工作流 |
| epi_formal/.git | 目录 | **已移除**（去指纹） |

## 二、受版本控制的源文件（52）

根级（9）：
README.md、PROOF_GAPS.md、LEMMA_AUDIT.md、FINAL_REVIEW.md、
lean-toolchain、lakefile.toml、lake-manifest.json、EpiFormal.lean、Audit.lean

EpiFormal/（43）：
AdjacentWitness、Alekseyev、AlgebraicIndependence、Axioms、Basic、Classification、
DefectFibres、DeltaReduction、DeltaSign、DimHCore、DimHFinite、Elementary、
Escape、EscapeBoundary、EscapeReduction、EulerConvergents、FactorialCriterion、
FlintHills、Measure、Meiburg、MeiburgConvergence、OpenAI_mu_pi_bridge、
PadeBoundary、PadeDeriv、PadeIntegral、PadeODE、PadeRecurrence、
QuarterPointCore、QuarterPointFinal、QuarterPointTail、Series、
SignedClusters、SignedCriterion、SpectralGap、Spectrum、ThresholdAttained、
WeightedCantor、WeightedDimHCore、WeightedFiber、WeightedFinal、
WeightedLower、WeightedPhase、WeightedUpper（均 .lean）

## 三、在 guest 内重建 git（可选）

```bash
cd ~/epi_work/epi_formal
git init -b main
git add -A
git -c user.name=cage -c user.email=cage@localhost commit -m "e+pi formal snapshot"
```

身份已为中性 cage，不会带入真实指纹。
