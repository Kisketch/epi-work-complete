# 论文二 Tex 切片日志（SLICE_LOG）

- 日期：2026-11-23
- 源文件：`paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex`
- 源文件规格：4064 行 / 253919 字节 / UTF-8 无 BOM / 全部 CRLF（4064 个 CRLF，无孤立 CR）/ 末尾有换行
- 切片目录：`paper2_spectral_gap_dimension/split/src_sections/`
- 原则：原版只读；仅按行号连续复制，不增删字符；每个碎片以 CRLF 结尾。
- 边界调整说明：`sec-windows` 取 **2814–3561**（不含 `sec:residues-asymptotic`），`sec-resasymp` 取 **3562–3702**（含 3701 正文行与 3702 空行）。这样 11 个碎片无重叠、无遗漏。若按题面把 windows 记为 2814–3702 会与 resasymp 3562–3701 重叠，故采用本切分；二者并集仍为 2814–3702。
- `sec-verification` 取 3786–4064，含 `\section*{Use of AI and formal verification}` 与 `\end{document}`，以便拼接覆盖全文。

## 一、切片清单

| 文件 | 起行 | 止行 | 行数 | 字节 | SHA-256 |
|---|---:|---:|---:|---:|---|
| sec-preface.tex | 1 | 389 | 389 | 24898 | 7f1e1318cbe990cff19ac62bba7b9202e50951dbe945fc1c519ab479b10158e6 |
| sec-class.tex | 390 | 477 | 88 | 3792 | 4df3799eb06c87ef4d497982f3f8e71983c80af58177258289d1bcce6cad68c1 |
| sec-spectrum.tex | 478 | 594 | 117 | 6666 | c75ab29f1f996ed09abe8e06331aeb2c9a8a40cedaab62406b2e4f7e98d5e88e |
| sec-finite.tex | 595 | 826 | 232 | 12099 | c83d8fa8f6ccc0c1731e2301f7241cead708ae14f0e84da03795c78f4392a036 |
| sec-weights.tex | 827 | 1176 | 350 | 17605 | e9346817f29a9a602dbbfc3d60dec39025a23dd7b5a9c30f69105e6bbfd72f49 |
| sec-gauge.tex | 1177 | 2500 | 1324 | 80784 | 14626ad5c7125d7c93744617ebb5c13df618198c6d7197853d53c6241d1b1cc0 |
| sec-growing.tex | 2501 | 2813 | 313 | 22045 | 739b426e8162361227ee1107cb6dcd1ed6af09b9fd5624c162086c97dd7e2be9 |
| sec-windows.tex | 2814 | 3561 | 748 | 48521 | 046757e32fa9173d6e02ce665faba8dcea822def0717088eb46825013ca1f323 |
| sec-resasymp.tex | 3562 | 3702 | 141 | 13614 | 083f0049d310c602e545cb5125a08309ba4d808dfdd4ac6fa0189b6e034479be |
| sec-num.tex | 3703 | 3785 | 83 | 5306 | 5547fc76bf4d694170618881d3c7da79d59dc3e80ed207bbe549e2b9593923ce |
| sec-verification.tex | 3786 | 4064 | 279 | 18589 | 18e9685dd3b27ba0d82190bd08a29f28930b62bc55000b356b26ee0415453865 |

合计：11 个文件，4064 行，253919 字节。

说明：`sec-gauge.tex` 内含 `sec:finite-state-tail`（1817–1968）与 `sec:poly-rec`（1969–2500）；`sec-growing.tex` 为 2501–2813 单列。`slice_index.csv` 为同一清单的机器可读版本。

## 二、无损拼接校验

拼接顺序（严格原序）：

```
sec-preface.tex
sec-class.tex
sec-spectrum.tex
sec-finite.tex
sec-weights.tex
sec-gauge.tex
sec-growing.tex
sec-windows.tex
sec-resasymp.tex
sec-num.tex
sec-verification.tex
```

校验命令（PowerShell，在仓库根目录执行）：

```powershell
$ErrorActionPreference='Stop'
$src='paper2_spectral_gap_dimension\paper2_spectral_gap_dimension.tex'
$dir='paper2_spectral_gap_dimension\split\src_sections'
$order=@('sec-preface.tex','sec-class.tex','sec-spectrum.tex','sec-finite.tex',
         'sec-weights.tex','sec-gauge.tex','sec-growing.tex','sec-windows.tex',
         'sec-resasymp.tex','sec-num.tex','sec-verification.tex')
$enc=New-Object System.Text.UTF8Encoding($false)
$sb=New-Object System.Text.StringBuilder
foreach($f in $order){ [void]$sb.Append([System.IO.File]::ReadAllText((Join-Path $dir $f))) }
$tmp=Join-Path $env:TEMP 'paper2_reassembled_check.tex'
[System.IO.File]::WriteAllText($tmp,$sb.ToString(),$enc)
$sha=[System.Security.Cryptography.SHA256]::Create()
$h1=[BitConverter]::ToString($sha.ComputeHash([System.IO.File]::ReadAllBytes($src))).Replace('-','').ToLower()
$h2=[BitConverter]::ToString($sha.ComputeHash([System.IO.File]::ReadAllBytes($tmp))).Replace('-','').ToLower()
"src_sha256=$h1"
"asm_sha256=$h2"
"byte_equal=$($h1 -eq $h2)"
"src_bytes=$((Get-Item $src).Length) asm_bytes=$((Get-Item $tmp).Length)"
```

实际输出：

```
src_sha256=3f6b9b27e08a2699bf40df5bf4a167527f277f783eef52410fd8bbf697641769
asm_sha256=3f6b9b27e08a2699bf40df5bf4a167527f277f783eef52410fd8bbf697641769
byte_equal=True
src_bytes=253919 asm_bytes=253919
```

结论：逐字节一致（不是仅末尾换行等价，而是完全相同），无字符增删，无 BOM 差异。校验用临时文件：`%TEMP%\paper2_reassembled_check.tex`（未写入项目目录）。

## 三、声明

- 未修改原版 `.tex`，未触碰 `historical_versions/`、`verification/`、`epi_formal/`。
- 三轨草案仅含导言占位、`\input` 引用与注释，未复制任何正文。
- 草案中对子段（gauge 前半 1177–1816、finite-state-tail 1817–1968、poly 1969–2500）的精确切分仍待正式抽正文时执行；当前 `sec-gauge.tex` 为整节切片。
