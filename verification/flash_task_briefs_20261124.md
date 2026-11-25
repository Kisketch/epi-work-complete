# flash 执行任务书（2026-11-24，v1）

> **分工**：分析、策略、提示词由主会话（GLM-5.4）负责；执行由临时子代理（GLM-5.3-Flash）完成。本文件是派给 flash 的任务书原文，每个任务自带目标、边界、步骤、验收与禁区，目的就是**一次做对、不返工**。
> **全局硬规则（每个任务都适用）**：只增不减——只允许新建文件，禁止修改/删除任何既有文件（含 .tex/.lean/.py/.md/.csv/.log/.json/.jsonl）；禁止 git 写操作；禁止运行 lake；禁止 pdflatex；禁止联网（E5 除外）。数值一律用 `.venv\Scripts\python.exe`（系统 python 无 mpmath）。先读 `AGENTS.md`。回答 ≤1000 字并给出产出文件的 workspace 相对路径；细节写进文件。
> **工作区**：`<repo-root>`（PowerShell 5.1）。

---

## E1｜论文二结构清单（供拆分评级用）→ 临时代理「论文二结构盘点」

**目标**：产出论文二主稿的逐节结构清单与切片/三轨映射，供主会话做拆分评级。只做抽取与核对，不做评价。

**对象（只读）**：
- `paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`（主稿，4463 行）
- `paper2_spectral_gap_dimension/split/`（`README.md`、`slice_index.csv`、`src_sections/*.tex`、`2A_core_gauge_trichotomy/`、`2B_general_theory/`、`2C_windows_residues_finstate/`、`S_supplement/`）
- `paper2_spectral_gap_dimension/README.md`

**步骤**：
1. 章节表：`rg -n '^\\section\{|^\\subsection\{' paper2_spectral_gap_dimension\paper2_spectral_gap_dimension.tex`，得到每个 section/subsection 的行号；区间 = 本标题行到下一标题行前一行；每个区间用 `(Get-Content <tex>)[a..b] | Measure-Object -Word` 统计词数。
2. 标签统计：对每个区间 `rg -n -o '\\label\{[^}]+\}'`，按前缀分类计数（thm/lem/prop/cor/def/rem/exa/tab/sec/eq/其他），并列出全部 thm/lem/prop/cor 的 label 名。
3. Lean 映射：对每个区间 `rg -n -o '[A-Za-z0-9_]+\.lean'`，列出出现的 .lean 文件名（去重）。
4. 切片映射：读 `split/slice_index.csv` 得到基础切片顺序；对每个切片文件用首行与末行在主稿中 `rg -n -F` 定位，输出「切片 | 文件 | 行数 | 主稿起行 | 主稿止行」；核对相邻区间连续（止行+1=下一起行）且总数=4463。
5. 逐字节核对（不改任何文件）：按切片顺序把 `src_sections/*.tex` 的字节拼接后与主稿比 SHA-256：
   ```powershell
   $order = (Import-Csv paper2_spectral_gap_dimension\split\slice_index.csv | Select-Object -First 11)  # 若列名不同，按文件内容自行解析顺序
   $ms = New-Object System.IO.MemoryStream
   foreach ($s in $order) { $f = "paper2_spectral_gap_dimension\split\src_sections\$($s.name).tex"; if (-not (Test-Path $f)) { $f = "paper2_spectral_gap_dimension\split\src_sections\$($s.file)" }; $b=[System.IO.File]::ReadAllBytes($f); $ms.Write($b,0,$b.Length) }
   $ms.Position=0; $h=[System.Security.Cryptography.SHA256]::Create().ComputeHash($ms); ([System.BitConverter]::ToString($h)) -replace '-',''
   (Get-FileHash paper2_spectral_gap_dimension\paper2_spectral_gap_dimension.tex -Algorithm SHA256).Hash
   ```
   两个哈希一致即逐字节同源；不一致则报告首个差异行（用 `Compare-Object` 逐行比对）。
6. 三轨一补：列出 `2A_core_gauge_trichotomy/`、`2B_general_theory/`、`2C_windows_residues_finstate/`、`S_supplement/` 各自的 .tex/.pdf/.log 文件（名称、大小）；对每轨主 tex 用 `rg -n '\\input\{|\\include\{|^\\section\{'` 列出其包含的章节；从各轨最新 .log 统计 `Undefined`、`Error`、`Overfull` 出现次数；对照 `split/README.md` 与 `paper2_spectral_gap_dimension/README.md` 中声明的页数与章节归属，报告「声明 vs 实际」。
7. `git status --porcelain=v1` 确认只有未跟踪新文件，无 ` M` 行。

**产出（新文件）**：
- `verification/paper2_structure_inventory_20261124.md`：①章节表（section | 行区间 | 词数 | 各类标签计数 | thm/lem/prop/cor 列表 | Lean 文件）；②切片映射表 + 哈希结论；③三轨一补表（轨 | 文件 | 大小 | 包含章节 | 日志错误/未定义/Overfull | 声明页数）。
- `verification/paper2_section_map_20261124.csv`：列 `level,title,start_line,end_line,words,thm,lem,prop,cor,def,rem,lean_files`。

**验收**：章节表覆盖全部 section/subsection；切片表 11 行且连续、总数 4463；哈希结论明确（一致/不一致+首差异行）；三轨表四行齐全；无既有文件被修改。
**禁区**：评价、打分、改写建议（那是主会话的事）；修改任何文件；pdflatex；lake；联网。

---

## E3｜临界扫描扩展与标度复核 → 临时代理「临界扫描扩展」

**目标**：按既定脚本把近临界族补齐到 j=16，并把两个最近临界集合推进到 m=32768/65536，然后重跑诊断与标度复核，写增补记录。全部数值来自脚本真实输出（类别 4）。

**先读（必须）**：`verification/critical_point_scan_record_20261124.md` §2、§5（方法与模型）；`verification/critical_point_scan_20261124.py` 头注（阶段与配置格式）。

**步骤**：
1. 新建配置 `verification/critical_point_scan_20261124_config_ext.json`（格式照 `_config.json`）：`n=16`，`n_check=24`，`n_check_m=[4096]`，`m_list=[16,32,64,128,256,512,1024,2048,4096,8192,16384]`，sets 共 8 组：`S=[3,4,5,6,j]`，j∈{13,14,15,16}，各配 `B=[]` 与 `B=[1]`，`center` 全部为 `"0.5"`（这四个 S 的 s₀<1/2，见记录 §3）。
2. 新建配置 `verification/critical_point_scan_20261124_config_deep.json`：`n=16`，`n_check_m=[]`，`m_list=[32768,65536]`，sets 两组：`S=[3,4,5,6,9]` center `"0.50240618989678084139388234905"`；`S=[3,4,5,6,10]` center `"0.5"`，均 `B=[]`。
3. 运行（每条若超过 10 分钟就用 `Start-Process` 后台并轮询其 .log 直到出现 `new points`）：
   `.venv\Scripts\python.exe verification\critical_point_scan_20261124.py scan verification\critical_point_scan_20261124_config_ext.json`
   `.venv\Scripts\python.exe verification\critical_point_scan_20261124.py scan verification\critical_point_scan_20261124_config_deep.json`
   脚本按 key 断点续跑，重复运行安全。
4. 重跑诊断与复核，输出到**新的**文件（不得覆盖 v1 输出）：
   `.venv\Scripts\python.exe verification\critical_point_scan_analyze_20261124.py | Out-File -Encoding utf8 verification\critical_point_scan_20261124_diagnostics_v2.md`
   `.venv\Scripts\python.exe verification\critical_scaling_check_20261124.py | Out-File -Encoding utf8 verification\critical_scaling_check_20261124_output_v2.md`
5. 写增补 `verification/critical_point_scan_addendum_20261124.md`：
   - 表 A：j=13–16（B=∅ 与 B={1}）在 m=1024/4096/16384 的 `ratio obs/model`（从 v2 复核输出摘录）与 `alpha_loc`（从 v2 诊断摘录）；
   - 表 B：m=32768、65536 的 `dim`、`Δ=dim−center`、相对 m=16384 的局部指数、`ratio obs/model`；
   - 结论只写数据事实（例如「比值继续趋近 1 / 出现偏离」），标注「类别 4，数值佐证非证明」，不作定理性断言。
6. `git status --porcelain=v1` 确认只有未跟踪新文件。

**验收**：JSONL 新增 ≥ 92 条 scan 记录；两个 v2 输出文件存在；增补文件含表 A、表 B；无既有文件被修改。
**禁区**：改任何既有文件（含 v1 输出与 JSONL 以外的既有文件——JSONL 只追加）；lake；pdflatex；联网；心算填数；自行改脚本。

---

## E5｜期刊版图（可选，需联网）→ 临时代理「期刊版图」

**目标**：为论文二三轨一补各找 6–10 本候选期刊（含 2–3 本顶刊与 3–5 本强专业刊），每本给 2 篇近年（2020–2026） representative 论文（标题、作者、年份、期刊卷页或 DOI、URL），主题限定：连分数集/极限集的 Hausdorff 维数、热力学形式体系与相变、Mauldin–Urbanski 无限 IFS 维数、Kesseböhmer–Stratmann/Munday 一系、有限状态/图导向集维数。

**方法**：用 web 搜索与抓取；**书目字段只能来自实际打开的页面**；打不开的写「未核到」；不得凭记忆补全。无 web 工具则回答「无 web 工具，未执行」。

**产出（新文件）**：`verification/journal_landscape_20261124.md`：按轨分节（2A/2B/2C/S），每节一张表（期刊 | 类型 顶刊/强专业刊 | 匹配理由 ≤30 字 | 代表论文 2 条 | URL）；末尾注明检索日期与覆盖范围（负搜索≠不存在）。
**禁区**：评价本论文能否中刊；修改任何文件。
