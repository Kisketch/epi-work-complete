# 整理续跑_20261121.ps1 — 剩余步骤（只移动，零删除）
$ErrorActionPreference='Stop'
$root = 'C:\Users\Lgnatius\Documents\qwen-agent\QOTCWZPRRA\default\epi_work'
$P1   = Join-Path $root '论文一_e_plus_pi'
$P2   = Join-Path $root '论文二_谱隙与维数'

function Count-Files { (Get-ChildItem $root -Recurse -File -Force | Where-Object { $_.FullName -notmatch '\\\.venv\\' } | Measure-Object).Count }
$before = Count-Files
Write-Output "BEFORE file count (excl .venv): $before"

# ---------- 4 续. 根目录旧构建日志 ----------
foreach ($f in @('lean_build_verify.log','lean_audit_verify.log','gx_out.txt')) {
  if (Test-Path (Join-Path $root $f)) { Move-Item (Join-Path $root $f) "$P1\04_形式化核查\旧构建日志\$f" }
}

# ---------- 5. 研究过程（原 parallel_work 整目录更名；合稿Lean审计.txt 随之迁移） ----------
Move-Item "$P1\parallel_work" "$P1\05_研究过程"
Move-Item "$P1\Parallel_Research_Plan.md" "$P1\05_研究过程\Parallel_Research_Plan.md"

# ---------- 6. 历史版本 ----------
Move-Item "$P1\连续三轮修订" "$P1\06_历史版本\连续三轮修订"
Move-Item "$P1\历史归档" "$P1\06_历史版本\归档快照\修订前快照"
Move-Item (Join-Path $root '论文一_e_plus_pi.zip') "$P1\06_历史版本\归档快照\论文一_e_plus_pi.zip"
Move-Item "$root\papers\第一阶段_e_plus_pi.tex" "$P1\06_历史版本\归档快照\papers旧版\第一阶段_e_plus_pi.tex"
Move-Item "$root\papers\第一阶段_e_plus_pi.pdf" "$P1\06_历史版本\归档快照\papers旧版\第一阶段_e_plus_pi.pdf"
Get-ChildItem "$root\papers\archive" -File | ForEach-Object { Move-Item $_.FullName "$P1\06_历史版本\归档快照\papers旧版\$($_.Name)" }
Get-ChildItem "$root\papers" -File -Filter *.md | ForEach-Object { Move-Item $_.FullName "$P1\06_历史版本\参考文档\$($_.Name)" }
Move-Item "$root\submission_packages\paper1_e_plus_pi_source.zip" "$P1\06_历史版本\归档快照\投稿快照_paper1.zip"
Move-Item "$root\submission_packages\epi_formal_repro_bundle.zip" "$P1\06_历史版本\归档快照\投稿快照_epi_formal_repro.zip"

# ---------- 7. 论文二历史版本 ----------
Move-Item "$root\papers\第二阶段_谱隙与维数.tex" "$P2\历史版本\第二阶段_谱隙与维数_旧版.tex"
Move-Item "$root\papers\第二阶段_谱隙与维数.pdf" "$P2\历史版本\第二阶段_谱隙与维数_旧版.pdf"
if (Test-Path "$root\papers\numerics") { Move-Item "$root\papers\numerics" "$P2\历史版本\numerics" }
Move-Item "$root\submission_packages\paper2_spectral_gap_dimension_source.zip" "$P2\历史版本\投稿快照_paper2.zip"

# ---------- 8. 清空后的目录移除（仅空目录） ----------
foreach ($d in @("$root\papers\archive", "$root\papers", "$root\submission_packages", "$P1\第二阶段修订\formalization", "$P1\第二阶段修订")) {
  if (Test-Path $d) {
    $remaining = (Get-ChildItem $d -Recurse -Force | Measure-Object).Count
    if ($remaining -eq 0) { Remove-Item $d | Out-Null; Write-Output "removed empty dir: $d" }
    else { Write-Output "NOT EMPTY, kept: $d ($remaining items)" }
  }
}

$after = Count-Files
Write-Output "AFTER  file count (excl .venv): $after"
if ($after -ne $before) { Write-Output "!!! FILE COUNT MISMATCH"; exit 1 } else { Write-Output "CONSERVATION OK" }
Write-Output ""
Write-Output "=== final workspace tree (depth 2) ==="
Get-ChildItem $root | Where-Object { $_.Name -notmatch '^(\.venv|\.agents|epi_formal)$' } | ForEach-Object {
  Write-Output ("+ " + $_.Name)
  if ($_.PSIsContainer -and $_.Name -match '^论文') {
    Get-ChildItem $_.FullName | ForEach-Object { Write-Output ("  + " + $_.Name) }
  }
}
