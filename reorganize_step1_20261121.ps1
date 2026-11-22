# 整合整理_20261121.ps1 — 论文文件夹整合（只移动，零删除）
# 守恒纪律：移动前后工作区文件总数必须相等；Move-Item 不带 -Force，天然防覆盖。
$ErrorActionPreference='Stop'
$root = 'C:\Users\Lgnatius\Documents\qwen-agent\QOTCWZPRRA\default\epi_work'
$P1   = Join-Path $root '论文一_e_plus_pi'
$P2   = Join-Path $root '论文二_谱隙与维数'

function Count-Files { (Get-ChildItem $root -Recurse -File -Force | Where-Object { $_.FullName -notmatch '\\\.venv\\' } | Measure-Object).Count }
$before = Count-Files
Write-Output "BEFORE file count (excl .venv): $before"

# ---------- 目标目录 ----------
$dirs = @(
  "$P1\01_主稿", "$P1\02_伴随稿", "$P1\04_形式化核查", "$P1\04_形式化核查\旧构建日志",
  "$P1\06_历史版本", "$P1\06_历史版本\主稿备份", "$P1\06_历史版本\归档快照\papers旧版",
  "$P1\06_历史版本\参考文档", "$P2\历史版本"
)
foreach ($d in $dirs) { if (-not (Test-Path $d)) { New-Item -ItemType Directory -Path $d | Out-Null } }

# ---------- 1. 主稿 ----------
foreach ($f in @('第一阶段_e_plus_pi.tex','第一阶段_e_plus_pi.pdf','第一阶段_e_plus_pi.aux','第一阶段_e_plus_pi.log','第一阶段_e_plus_pi.out','assemble_restructure.ps1')) {
  Move-Item (Join-Path $P1 $f) (Join-Path $P1 "01_主稿\$f")
}
# 备份 → 历史版本
Move-Item "$P1\第一阶段_e_plus_pi.backup_20261121.tex" "$P1\06_历史版本\主稿备份\第一阶段_e_plus_pi.backup_20261121.tex"

# ---------- 2. 伴随稿（原 第二阶段修订\ 根文件） ----------
foreach ($f in @('Phase2_revised.tex','Phase2_revised.pdf','Phase2_revised.aux','Phase2_revised.log','Phase2_revised.out')) {
  Move-Item "$P1\第二阶段修订\$f" "$P1\02_伴随稿\$f"
}
Move-Item "$P1\第二阶段修订\pdflatex_verify.log" "$P1\04_形式化核查\pdflatex_verify.log"

# ---------- 3. 投稿准备（整目录） ----------
Move-Item "$P1\第二阶段修订\投稿准备" "$P1\03_投稿准备"

# ---------- 4. 形式化核查 ----------
Get-ChildItem "$P1\第二阶段修订\formalization" -File | ForEach-Object { Move-Item $_.FullName "$P1\04_形式化核查\$($_.Name)" }
foreach ($f in @('DenominatorCertificate.lean','UnweightedCorrection.lean','合稿Lean审计.txt')) {
  Move-Item (Join-Path $P1 $f) "$P1\04_形式化核查\$f"
}
# 工作区根的旧构建日志
foreach ($f in @('lean_build_verify.log','lean_audit_verify.log','gx_out.txt')) {
  Move-Item (Join-Path $root $f) "$P1\04_形式化核查\旧构建日志\$f"
}

# ---------- 5. 研究过程（原 parallel_work 整目录更名） ----------
Move-Item "$P1\parallel_work" "$P1\05_研究过程"
Move-Item "$P1\Parallel_Research_Plan.md" "$P1\05_研究过程\Parallel_Research_Plan.md"

# ---------- 6. 历史版本 ----------
Move-Item "$P1\连续三轮修订" "$P1\06_历史版本\连续三轮修订"
Move-Item "$P1\历史归档" "$P1\06_历史版本\归档快照\修订前快照"
Move-Item (Join-Path $root '论文一_e_plus_pi.zip') "$P1\06_历史版本\归档快照\论文一_e_plus_pi.zip"
# papers\ 中论文一旧版与归档
Move-Item "$root\papers\第一阶段_e_plus_pi.tex" "$P1\06_历史版本\归档快照\papers旧版\第一阶段_e_plus_pi.tex"
Move-Item "$root\papers\第一阶段_e_plus_pi.pdf" "$P1\06_历史版本\归档快照\papers旧版\第一阶段_e_plus_pi.pdf"
Get-ChildItem "$root\papers\archive" -File | ForEach-Object { Move-Item $_.FullName "$P1\06_历史版本\归档快照\papers旧版\$($_.Name)" }
# papers\ 中的参考文档
Get-ChildItem "$root\papers" -File -Filter *.md | ForEach-Object { Move-Item $_.FullName "$P1\06_历史版本\参考文档\$($_.Name)" }
# 投稿快照 zip
Move-Item "$root\submission_packages\paper1_e_plus_pi_source.zip" "$P1\06_历史版本\归档快照\投稿快照_paper1.zip"
Move-Item "$root\submission_packages\epi_formal_repro_bundle.zip" "$P1\06_历史版本\归档快照\投稿快照_epi_formal_repro.zip"

# ---------- 7. 论文二历史版本 ----------
Move-Item "$root\papers\第二阶段_谱隙与维数.tex" "$P2\历史版本\第二阶段_谱隙与维数_旧版.tex"
Move-Item "$root\papers\第二阶段_谱隙与维数.pdf" "$P2\历史版本\第二阶段_谱隙与维数_旧版.pdf"
if (Test-Path "$root\papers\numerics") { Move-Item "$root\papers\numerics" "$P2\历史版本\numerics" }
Move-Item "$root\submission_packages\paper2_spectral_gap_dimension_source.zip" "$P2\历史版本\投稿快照_paper2.zip"

# ---------- 8. 清空后的目录移除（仅空目录，无文件损失） ----------
foreach ($d in @("$root\papers\archive", "$root\papers", "$root\submission_packages", "$P1\第二阶段修订\formalization", "$P1\第二阶段修订")) {
  if (Test-Path $d) {
    $remaining = (Get-ChildItem $d -Recurse -Force | Measure-Object).Count
    if ($remaining -eq 0) { Remove-Item $d | Out-Null; Write-Output "removed empty dir: $d" }
    else { Write-Output "NOT EMPTY, kept: $d ($remaining items)" }
  }
}

$after = Count-Files
Write-Output "AFTER  file count (excl .venv): $after"
if ($after -ne $before) { Write-Output "!!! FILE COUNT MISMATCH — INVESTIGATE"; exit 1 } else { Write-Output "CONSERVATION OK" }
