# rename_english_20261121.ps1 — 全英文命名（只改名，零删除，守恒校验）
$ErrorActionPreference='Stop'
$root = 'C:\Users\Lgnatius\Documents\qwen-agent\QOTCWZPRRA\default\epi_work'
function Count-Files { (Get-ChildItem $root -Recurse -File -Force | Where-Object { $_.FullName -notmatch '\\\.venv\\' } | Measure-Object).Count }
$before = Count-Files
Write-Output "BEFORE: $before"

function RN([string]$path,[string]$new){ if (Test-Path -LiteralPath $path) { Rename-Item -LiteralPath $path -NewName $new } else { Write-Output "SKIP (not found): $path" } }

# ---------- Phase 1: 工作区根 ----------
RN "$root\论文一_e_plus_pi" 'paper1_e_plus_pi'
RN "$root\论文二_谱隙与维数" 'paper2_spectral_gap_dimension'
RN "$root\进度与路径分析.md" 'progress_and_path_analysis.md'
RN "$root\整合整理_20261121.ps1" 'reorganize_step1_20261121.ps1'
RN "$root\整理续跑_20261121.ps1" 'reorganize_step2_20261121.ps1'
$P1 = "$root\paper1_e_plus_pi"
$P2 = "$root\paper2_spectral_gap_dimension"

# ---------- Phase 2: P1 顶层 ----------
RN "$P1\00_项目索引.md" '00_PROJECT_INDEX.md'
RN "$P1\00_当前研究路径与进度.md" '00_research_status.md'
RN "$P1\00_合稿核查与价值分析.md" '00_merge_review.md'
RN "$P1\01_主稿" '01_main_paper'
RN "$P1\02_伴随稿" '02_companion_paper'
RN "$P1\03_投稿准备" '03_submission_prep'
RN "$P1\04_形式化核查" '04_formalization_audits'
RN "$P1\05_研究过程" '05_research_process'
RN "$P1\06_历史版本" '06_historical_versions'

# ---------- Phase 3: 主稿文件改名 ----------
foreach ($ext in @('tex','pdf','aux','log','out')) {
  RN "$P1\01_main_paper\第一阶段_e_plus_pi.$ext" "paper1_e_plus_pi.$ext"
}
RN "$P1\06_historical_versions\main_backups\第一阶段_e_plus_pi.backup_20261121.tex" 'paper1_e_plus_pi.backup_20261121.tex'

# ---------- Phase 4: 子目录英文化 ----------
RN "$P1\04_formalization_audits\旧构建日志" 'old_build_logs'
RN "$P1\05_research_process\公共谱密度与立方根频率" 'spectrum_density_cubic_root_frequency'
RN "$P1\05_research_process\十轮推进" 'round10_advance'
RN "$P1\05_research_process\定理深化" 'theorem_deepening'
RN "$P1\05_research_process\研究续推" 'research_continuation'
RN "$P1\05_research_process\窗口阶乘频率" 'window_factorial_frequency'
RN "$P1\05_research_process\精确临界振幅和任意区间谱计数" 'sharp_amplitude_interval_counting'
RN "$P1\05_research_process\轨道交集与有限状态频率" 'orbit_intersection_finite_state_frequency'
RN "$P1\05_research_process\合稿Lean审计.txt" 'merge_lean_audit.txt'
RN "$P1\06_historical_versions\主稿备份" 'main_backups'
RN "$P1\06_historical_versions\连续三轮修订" 'rounds_04_08'
RN "$P1\06_historical_versions\归档快照" 'archive_snapshots'
RN "$P1\06_historical_versions\参考文档" 'reference_docs'
RN "$P1\06_historical_versions\archive_snapshots\papers旧版" 'papers_old'
RN "$P1\06_historical_versions\archive_snapshots\修订前快照" 'pre_revision_snapshots'

# rounds_04_08 内部子目录
RN "$P1\06_historical_versions\rounds_04_08\04_短窗口的几乎处处定理" '04_short_window_ae_theorem'
RN "$P1\06_historical_versions\rounds_04_08\05_零测度与满维数" '05_zero_measure_full_dimension'
RN "$P1\06_historical_versions\rounds_04_08\06_有理仿射窗口" '06_rational_affine_windows'
RN "$P1\06_historical_versions\rounds_04_08\07_Lean递推审计" '07_lean_recurrence_audit'
RN "$P1\06_historical_versions\rounds_04_08\08_部分商判据与研究路线" '08_partial_quotient_criteria'

# ---------- Phase 5: 投稿准备 md ----------
RN "$P1\03_submission_prep\复核与投稿信草稿.md" 'review_cover_letter_draft.md'
RN "$P1\03_submission_prep\投稿准备记录.md" 'submission_prep_notes.md'
RN "$P1\03_submission_prep\期刊政策记录.md" 'journal_policy_notes.md'
RN "$P1\03_submission_prep\清单核查与下一步计划.md" 'checklist_next_steps.md'

# ---------- Phase 6: 参考文档 md + papers_old ----------
RN "$P1\06_historical_versions\reference_docs\两篇论文审查总结.md" 'two_paper_review_summary.md'
RN "$P1\06_historical_versions\reference_docs\存量审计报告.md" 'legacy_audit_report.md'
RN "$P1\06_historical_versions\reference_docs\项目交接总纲.md" 'project_handover.md'
RN "$P1\06_historical_versions\reference_docs\δ符号交替定理的严格数学证明.md" 'delta_sign_alternation_proof.md'
RN "$P1\06_historical_versions\reference_docs\加权相变上界定理.md" 'weighted_transition_upper_bound.md'
RN "$P1\06_historical_versions\archive_snapshots\papers_old\进度与路径分析.md" 'progress_notes_20261118.md'
foreach ($ext in @('tex','pdf','aux','log','out')) {
  RN "$P1\06_historical_versions\archive_snapshots\papers_old\第一阶段_e_plus_pi_20261118.$ext" "paper1_e_plus_pi_20261118.$ext"
}

# ---------- Phase 7: 论文二 ----------
RN "$P2\历史版本" 'historical_versions'
foreach ($ext in @('tex','pdf')) {
  RN "$P2\第二阶段_谱隙与维数.$ext" "paper2_spectral_gap_dimension.$ext"
  RN "$P2\historical_versions\第二阶段_谱隙与维数_旧版.$ext" "paper2_old.$ext"
}

# ---------- Phase 8: 中文 zip 外名英文化（递归映射） ----------
$zipMap = [ordered]@{
  '2026-11-20_Antigravity接续前版.zip'              = '2026-11-20_pre_antigravity.zip'
  '2026-11-20_十轮合入前版.zip'                     = '2026-11-20_pre_round10_merge.zip'
  '2026-11-20_合稿前版.zip'                         = '2026-11-20_pre_merge.zip'
  '2026-11-20_复核前主稿.zip'                       = '2026-11-20_pre_review_main.zip'
  '2026-11-20_本轮研究前版.zip'                     = '2026-11-20_pre_research_round.zip'
  '2026-11-20_精确振幅与任意区间修订前版.zip'        = '2026-11-20_pre_sharp_amplitude_revision.zip'
  '2026-11-20_谱密度与立方根修订前版.zip'            = '2026-11-20_pre_spectrum_cubic_revision.zip'
  '2026-11-20_轨道交集与频率修订前版.zip'            = '2026-11-20_pre_orbit_frequency_revision.zip'
  '2026-11-21_一般递推精确维数修订前版.zip'          = '2026-11-21_pre_general_recurrence_revision.zip'
  '2026-11-21_有限状态缺陷尾部修订前版.zip'          = '2026-11-21_pre_finite_state_tail_revision.zip'
  'e_plus_pi_第07轮Lean核查与修订.zip'               = 'e_plus_pi_round07_lean_audit.zip'
  'e_plus_pi_第08轮研究进展与论文.zip'               = 'e_plus_pi_round08_research.zip'
  'e_plus_pi_第三轮评审修订.zip'                     = 'e_plus_pi_round03_review.zip'
  'e_plus_pi_论文分类交付.zip'                       = 'e_plus_pi_categorized_delivery.zip'
  'e_plus_pi_连续三轮修订_04至06.zip'                = 'e_plus_pi_rounds_04_06.zip'
}
foreach ($old in $zipMap.Keys) {
  $hits = Get-ChildItem $P1 -Recurse -File -Filter $old
  foreach ($h in $hits) { Rename-Item -LiteralPath $h.FullName -NewName $zipMap[$old]; Write-Output "zip: $old -> $($zipMap[$old])" }
}

$after = Count-Files
Write-Output "AFTER: $after"
if ($after -ne $before) { Write-Output "!!! FILE COUNT MISMATCH"; exit 1 } else { Write-Output "CONSERVATION OK" }

# 剩余中文目录/文件扫描（应只剩过程记录内容文件）
Write-Output ""
Write-Output "=== remaining Chinese-named DIRECTORIES (should be none) ==="
Get-ChildItem $root -Recurse -Directory | Where-Object { $_.Name -match '[\u4e00-\u9fff]' } | ForEach-Object { Write-Output $_.FullName.Replace($root,'') }
