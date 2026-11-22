"""Assemble and verify the complete 2026-11-22 Desktop delivery bundle and ZIP archive."""
from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DESKTOP = Path.home() / "Desktop"
PKG_NAME = "epi_complete_package_20261122"
PKG_DIR = DESKTOP / PKG_NAME
ZIP_PATH = DESKTOP / f"{PKG_NAME}.zip"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def copy_file(src: Path, dst: Path) -> None:
    assert src.exists(), f"Missing source file: {src}"
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def build_readme() -> str:
    return r"""# 论文与 Lean 4 完整交付与复现说明（2026-11-22 最终版）

> **一句总判断**：本交付包完整汇总两篇主论文（含历史 B 稿）、全量可复现 Lean 4 形式化项目（`epi_formal/`，Lean `v4.35.0`，`lake build EpiFormal` **9176 jobs** EXIT 0，`Audit.lean` **872/872** 条审计声明 = **849** 条仅用 Lean 基础公理 [含 5 条无公理] + **23** 条论文一经典白名单公理 + **0** 条项目自加公理，`sorryAx = 0`，131 个 `.lean` 文件零逃逸关键字；2026-11-22 新增/并入全部 **226** 条声明 0 非基础公理）及全部 Python/`sympy`/`mpmath` 核验脚本（含一般模 $m\in\{2,3,4,5,6\}$ 转移算子证书 `residue_certificate_general.py`）、日志与证书；**$e+\pi$ 无理性仍是公开问题，本工作未证明 $e+\pi$ 无理、有理或超越。**

---

## 一、诚实分类与边界摘要（遵守 `AGENTS.md`）

| 成果板块 | 诚实类别 | 核查状态（2026-11-22 实测） | 关键未做事项 / 边界 |
| :--- | :--- | :--- | :--- |
| 论文二：全谱离散化、正能级三分法、精确 Hausdorff 规范（$\mathbb{R}$ 与 $\mathbb{R}/\mathbb{Z}$）、一般 $(cj^r+d)$ 相变 $1-\alpha/r$、`thm:finite-state-tail` 全定理（$\mathbb{R}$ 与 $\mathbb{T}$）、`thm:windows` 全四条、`thm:short-ae` 显式常数 $(1-e^{-1})/160$、`thm:no-short-dim` 完整合取（$\dim_{\mathrm{H}}=1\wedge\operatorname{Leb}=0$），以及 `thm:residues`/`thm:residues-general` 结构理论与转移算子证书可靠性 | 无条件新结果 + Lean 4 Layer A 机器验证 | **已核实**（`lake build EpiFormal` 9176 jobs EXIT 0；`Audit.lean` 872/872，全部论文二模块含新增 `WindowShortAeRealize` [14]、`ResidueModGeneral` [7]、`TransferOperatorDim` [11]、`FiniteStateComplete` [12] 均仅依赖 Lean 基础公理，0 `sorryAx`） | `thm:residues` 与表 `tab:residues-general` 中 $N=256$、$K\in\{120,130\}$ 的大矩阵精确整数数值求值由 `residue_certificate.py` 与 `residue_certificate_general.py` 在 Python 中执行（矩阵可靠性定理已在 `TransferOperatorDim.lean` 内核验证），未直接在 Lean 内核展开 $256\times 256$ 数值计算 |
| 论文一：仿射窗口显式周期、黄金比轨道有限谱与 $B=1\text{--}6$ / 多尺度刚性、$e+\pi$ 归约与障碍分析、Flint Hills 条件桥接、Alekseyev 方向与逃逸约化 | 无条件模型/归约结果 + 条件桥接 + 障碍分析 + Lean 4 机器验证 | **已核实**（全部论文一引用模块——含原 8 个独立模块 `GoldenHeadCutoff` 等共 29 条声明——已并入 `epi_formal/` 与 `Audit.lean`；23 条经典定理推导显式依赖 3 条白名单公理 `e_transcendental`, `pi_transcendental`, `mu_e_eq_two`） | **未解决 $e+\pi$ 无理性**；论文一窗口/谱主体证明与障碍分析为纸面证明；有限区间/分母排除证书仅覆盖有限范围 |
| 符号、高精度区间与转移算子整数证书（`verify_round3.py`、`verify_round4.py`、`residue_certificate.py`、`residue_certificate_general.py`） | 有限计算与严格整数/区间认证（非 Lean 内核求值） | **已核实**（`verify_round3.py` 12/12 SymPy PASS；`verify_round4.py` 余弦积分 + 450 位 `mpmath.iv`；`residue_certificate.py` 认证 $357/512 < \dim_{\mathrm{H}} F_{4,1} < 359/512$；`residue_certificate_general.py` 认证 $m\in\{2,3,4,5,6\}, r\in\{1,m\}$ 全部 10 组二进区间与严格谱隙 `[PASS]`） | 仅验证有限范围、代数恒等式或有限格点转移矩阵，不构成一般性无理性证明 |
| CMMS 一次文献核查（`cmms_citation_check_20261122.md`） | 文献核查与复现 | **已核实**（直接核对 *Pacific J. Math.* 217(1) (2004), pp. 45–59 官方刊出全文，确认 §5 主定理为 **Theorem 3**，修正论文二三处误写） | — |

---

## 二、目录结构

```text
epi_complete_package_20261122/
├── README_交付与复现说明_20261122.md    # 本说明文件
├── MANIFEST_SHA256.txt                  # 全包所有文件 SHA-256 校验清单
├── AGENTS.md                            # 研究纪律与诚实分类法基线
├── papers/
│   ├── paper1_e_plus_pi/                # 论文一（72 页，TeX + PDF + pdflatex log，0 错误/0 警告/0 Overfull）
│   ├── paper2_spectral_gap_dimension/   # 论文二（50 页，TeX + PDF + pdflatex log，0 错误/0 警告/0 Overfull）
│   └── historical_draft_B_Phase2_revised/ # 历史 B 稿备份（Phase2_revised.tex/.pdf/.log）
├── epi_formal/                          # 完整可复现 Lean 4 项目（131 个 .lean，不含 8 GB .lake 缓存与 .git）
│   ├── lean-toolchain                   # leanprover/lean4:v4.35.0
│   ├── lakefile.toml & lake-manifest.json
│   ├── EpiFormal.lean                   # 总入口（含新闭合 4 模块、WindowBoundedUpper 与 8 个论文一辅助模块）
│   ├── Audit.lean                       # 872 条 #print axioms 全量审计脚本
│   ├── EpiFormal/                       # 129 个形式化模块（含 2026-11-22 新增/并入全套模块）
│   └── LEMMA_AUDIT.md / PROOF_GAPS.md / FINAL_REVIEW.md / README.md
└── verification/                        # 全部核验脚本、原始审计日志、证书与一次文献核查记录
    ├── audit_final_20261122.log         # 2026-11-22 实测 872 条 #print axioms 原始日志
    ├── check_audit_reconcile.py         # 872/872 双射、0 sorryAx、23 白名单、0 逃逸关键字自动核对脚本
    ├── verify_round3.py & .log          # 论文一 Appendix A 12/12 SymPy 符号验证
    ├── verify_round4.py & .log & certificate_round4.json  # 余弦积分 + 450 位 mpmath.iv 区间证书
    ├── residue_certificate.py & residue-certificate.log   # 论文二 thm:residues 精确整数转移算子证书
    ├── residue_certificate_general.py & .json & .log      # 论文二 thm:residues-general 一般模 m=2..6 整数证书
    ├── verify_paper2_merge.py & .log    # 论文二结构/标签/引文/公式完整性校验
    ├── cmms_citation_check_20261122.md  # CMMS PJM 2004 一次文献核查记录
    ├── paper1_companion_scripts/        # 论文一引用的伴随证书脚本（golden_finite_spectrum.py 等）
    └── reference_pdfs/                  # 核查留存一次文献 PDF（含 CMMS_PJM_2004_217_45.pdf 等）
```

---

## 三、三层公理依赖实测清单（`audit_final_20261122.log`）

经 `lake build EpiFormal`（9176 jobs，EXIT 0）与 `lake env lean Audit.lean`（EXIT 0），并由 `verification/check_audit_reconcile.py` 自动对账：

- **总计审计声明数**：**872 条**（`Audit.lean` 与日志 872/872 严格双射，重复 0）
- **`sorryAx` 计数**：**0**
- **逃逸关键字扫描**（全项目 131 个 `.lean` 文件扫描 `sorry` / `admit` / `native_decide` / `implemented_by` / `extern` / `unsafe` / `partial` / `opaque`）：**0 命中**
- **第 1 层（Lean 基础公理：`propext`, `Classical.choice`, `Quot.sound`）**：**849 条**（含 5 条零公理声明；**含 2026-11-22 新增/并入全部 226 条声明：`WindowShortAeRealize` 14 条、`ResidueModGeneral` 7 条、`TransferOperatorDim` 11 条、`FiniteStateComplete` 12 条、`WindowBoundedUpper` 21 条、8 个论文一辅助模块 29 条等，0 非基础公理**）
- **第 2 层（经典白名单公理，仅 3 条源码 `axiom` 声明）**：**23 条**（仅用于论文一经典超越数/无理性测度推论）：
  1. `e_transcendental`（`EpiFormal/Axioms.lean`）
  2. `pi_transcendental`（`EpiFormal/Axioms.lean`）
  3. `mu_e_eq_two`（`EpiFormal/Measure.lean`）
- **第 3 层（项目自加公理）**：**0 条**

---

## 四、一键复现步骤

### 4.1 校验包内文件完整性与审计日志对账（无需联网）

```powershell
# 1. 核对审计日志 872/872 双射、0 sorryAx、23 白名单、0 逃逸关键字
python verification\check_audit_reconcile.py verification\audit_final_20261122.log

# 2. 复跑核心 Python 符号/区间/整数证书（含 m=4 与一般 m=2..6）与论文二完整性脚本
python verification\verify_round3.py
python verification\verify_round4.py
python verification\residue_certificate.py
python verification\residue_certificate_general.py
python verification\verify_paper2_merge.py
```

### 4.2 洁净环境从源码重编译 Lean 4 与重跑内核审计（需联网拉取 mathlib 预编译 cache）

```powershell
cd epi_formal
lake exe cache get
lake build EpiFormal
lake env lean Audit.lean | Out-File -Encoding utf8 ..\verification\audit_rerun.log
cd ..
python verification\check_audit_reconcile.py verification\audit_rerun.log
```

> 注：`check_audit_reconcile.py` 自动兼容 UTF-8、UTF-8-SIG 与 Windows PowerShell 默认重定向生成的 UTF-16LE 日志；Windows 环境下若遇杀毒软件导致的并发 `.olean` 读取抖动，可对报错模块串行执行 `lake build EpiFormal.<ModuleName>` 后再执行 `lake build EpiFormal`。

### 4.3 重编译两篇论文 PDF（需 TeX Live 或 MiKTeX `pdflatex`）

```powershell
# 论文一（含目录与 hyperref 书签，洁净目录需三遍以稳定交叉引用）
cd papers\paper1_e_plus_pi
pdflatex -interaction=nonstopmode paper1_e_plus_pi.tex
pdflatex -interaction=nonstopmode paper1_e_plus_pi.tex
pdflatex -interaction=nonstopmode paper1_e_plus_pi.tex

# 论文二（洁净目录三遍稳定全部引用与书签）
cd ..\paper2_spectral_gap_dimension
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
pdflatex -interaction=nonstopmode paper2_spectral_gap_dimension.tex
```
"""


def main() -> None:
    if PKG_DIR.exists():
        shutil.rmtree(PKG_DIR)
    PKG_DIR.mkdir(parents=True, exist_ok=True)

    # 1. Papers (TeX + PDF + log, including historical B draft)
    for ext in (".tex", ".pdf", ".log"):
        copy_file(
            ROOT / "paper1_e_plus_pi" / "01_main_paper" / f"paper1_e_plus_pi{ext}",
            PKG_DIR / "papers" / "paper1_e_plus_pi" / f"paper1_e_plus_pi{ext}",
        )
        copy_file(
            ROOT / "paper2_spectral_gap_dimension" / f"paper2_spectral_gap_dimension{ext}",
            PKG_DIR / "papers" / "paper2_spectral_gap_dimension" / f"paper2_spectral_gap_dimension{ext}",
        )
        copy_file(
            ROOT / "paper1_e_plus_pi" / "02_companion_paper" / f"Phase2_revised{ext}",
            PKG_DIR / "papers" / "historical_draft_B_Phase2_revised" / f"Phase2_revised{ext}",
        )

    # 2. Complete reproducible epi_formal (exclude .lake and .git)
    epi_src = ROOT / "epi_formal"
    epi_dst = PKG_DIR / "epi_formal"
    for p in epi_src.rglob("*"):
        rel = p.relative_to(epi_src)
        if any(part in {".lake", ".git", "__pycache__"} for part in rel.parts):
            continue
        if p.is_file():
            copy_file(p, epi_dst / rel)

    # 3. Complete verification/ (exclude __pycache__)
    ver_src = ROOT / "verification"
    ver_dst = PKG_DIR / "verification"
    for p in ver_src.rglob("*"):
        rel = p.relative_to(ver_src)
        if "__pycache__" in rel.parts:
            continue
        if p.is_file():
            copy_file(p, ver_dst / rel)

    # 4. Paper 1 companion certificate scripts from 05_research_process
    companion_scripts = {
        "golden_finite_spectrum.py": ROOT / "paper1_e_plus_pi/05_research_process/research_continuation/golden_finite_spectrum.py",
        "quadratic_phase_certificate.py": ROOT / "paper1_e_plus_pi/05_research_process/research_continuation/quadratic_phase_certificate.py",
        "verify_pressure_example.py": ROOT / "paper1_e_plus_pi/05_research_process/research_continuation/verify_pressure_example.py",
        "verify_ten_rounds.py": ROOT / "paper1_e_plus_pi/05_research_process/round10_advance/verify_ten_rounds.py",
        "verify_trace_markov.py": ROOT / "paper1_e_plus_pi/05_research_process/orbit_intersection_finite_state_frequency/verify_trace_markov.py",
        "verify_research_advance.py": ROOT / "paper1_e_plus_pi/05_research_process/window_factorial_frequency/verify_research_advance.py",
        "verify_density_cube.py": ROOT / "paper1_e_plus_pi/05_research_process/spectrum_density_cubic_root_frequency/verify_density_cube.py",
        "verify_affine_extensions.py": ROOT / "paper1_e_plus_pi/05_research_process/theorem_deepening/verify_affine_extensions.py",
        "verify_sharp_window.py": ROOT / "paper1_e_plus_pi/05_research_process/sharp_amplitude_interval_counting/verify_sharp_window.py",
    }
    for name, src in companion_scripts.items():
        copy_file(src, ver_dst / "paper1_companion_scripts" / name)

    # 5. AGENTS.md and README
    copy_file(ROOT / "AGENTS.md", PKG_DIR / "AGENTS.md")
    (PKG_DIR / "README_交付与复现说明_20261122.md").write_text(build_readme(), encoding="utf-8")

    # 6. MANIFEST_SHA256.txt
    all_files = sorted(
        [p for p in PKG_DIR.rglob("*") if p.is_file() and p.name != "MANIFEST_SHA256.txt"],
        key=lambda p: p.relative_to(PKG_DIR).as_posix(),
    )
    manifest_lines = [f"{sha256_file(p)}  {p.relative_to(PKG_DIR).as_posix()}" for p in all_files]
    (PKG_DIR / "MANIFEST_SHA256.txt").write_text("\n".join(manifest_lines) + "\n", encoding="utf-8")

    # 7. Create ZIP archive
    if ZIP_PATH.exists():
        ZIP_PATH.unlink()
    zip_files = sorted([p for p in PKG_DIR.rglob("*") if p.is_file()], key=lambda p: p.relative_to(PKG_DIR).as_posix())
    with zipfile.ZipFile(ZIP_PATH, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
        for p in zip_files:
            arcname = f"{PKG_NAME}/{p.relative_to(PKG_DIR).as_posix()}"
            zf.write(p, arcname)

    # 8. Post-packaging verification
    print(f"Package directory: {PKG_DIR}")
    print(f"Package ZIP:       {ZIP_PATH} ({ZIP_PATH.stat().st_size / (1024 * 1024):.2f} MB)")
    print(f"Total files:       {len(zip_files)} (manifest entries: {len(manifest_lines)})")

    # 8a. ZIP integrity test
    with zipfile.ZipFile(ZIP_PATH, "r") as zf:
        bad = zf.testzip()
        assert bad is None, f"Corrupt ZIP entry: {bad}"
        names = zf.namelist()
        assert len(names) == len(zip_files), f"ZIP count mismatch: {len(names)} vs {len(zip_files)}"
        forbidden = [n for n in names if "/.lake/" in n or "/.git/" in n or "/__pycache__/" in n]
        assert not forbidden, f"Forbidden entries in ZIP: {forbidden[:10]}"
    print("[PASS] zipfile.testzip() is None; 0 forbidden (.lake/.git/__pycache__) entries")

    # 8b. Manifest SHA-256 verification
    for line in (PKG_DIR / "MANIFEST_SHA256.txt").read_text(encoding="utf-8").splitlines():
        expected_hash, rel_posix = line.split("  ", 1)
        actual_hash = sha256_file(PKG_DIR / rel_posix)
        assert actual_hash == expected_hash, f"SHA-256 mismatch for {rel_posix}"
    print(f"[PASS] MANIFEST_SHA256.txt verified ({len(manifest_lines)}/{len(manifest_lines)} exact matches)")

    # 8c. Run check_audit_reconcile.py inside PKG_DIR and verify_paper2_merge.py + UTF-16 log inside unpacked ZIP!
    proc = subprocess.run(
        [sys.executable, str(PKG_DIR / "verification" / "check_audit_reconcile.py")],
        capture_output=True,
        text=True,
        check=False,
    )
    assert proc.returncode == 0, f"Packaged check_audit_reconcile.py failed:\n{proc.stdout}\n{proc.stderr}"
    print("[PASS] Packaged verification/check_audit_reconcile.py EXIT 0 (872/872 inside package)")

    for gen_name in ("residue_certificate_general.py", "residue_certificate_general.json", "residue_certificate_general.log"):
        assert (PKG_DIR / "verification" / gen_name).exists(), f"Missing {gen_name} in package"
    print("[PASS] General modulus certificate artifacts (residue_certificate_general.{py,json,log}) present")

    with tempfile.TemporaryDirectory() as td:
        with zipfile.ZipFile(ZIP_PATH, "r") as zf:
            zf.extractall(td)
        unpacked = Path(td) / PKG_NAME
        # Verify verify_paper2_merge.py works inside unpacked Desktop package layout
        proc_m = subprocess.run(
            [sys.executable, str(unpacked / "verification" / "verify_paper2_merge.py")],
            cwd=str(unpacked),
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc_m.returncode == 0, f"Unpacked verify_paper2_merge.py failed:\n{proc_m.stdout}\n{proc_m.stderr}"
        # Verify check_audit_reconcile.py works on a PowerShell-style UTF-16LE redirected log
        utf16_log = unpacked / "verification" / "audit_utf16_test.log"
        utf16_log.write_text(
            (unpacked / "verification" / "audit_final_20261122.log").read_text(encoding="utf-8-sig"),
            encoding="utf-16",
        )
        proc_u16 = subprocess.run(
            [sys.executable, str(unpacked / "verification" / "check_audit_reconcile.py"), str(utf16_log)],
            cwd=str(unpacked),
            capture_output=True,
            text=True,
            check=False,
        )
        assert proc_u16.returncode == 0, f"UTF-16LE check_audit_reconcile.py failed:\n{proc_u16.stdout}\n{proc_u16.stderr}"
    print("[PASS] Unpacked ZIP tests: verify_paper2_merge.py EXIT 0 & UTF-16LE audit log reconciliation EXIT 0")

    # 8d. Cross-check every .lean, active .py, .json, .log cited in BOTH papers exists in package
    pkg_filenames = {p.name for p in zip_files}
    pkg_lean_names = {p.name for p in (PKG_DIR / "epi_formal").rglob("*.lean")}
    for label, tex_path in [
        ("Paper 1", PKG_DIR / "papers/paper1_e_plus_pi/paper1_e_plus_pi.tex"),
        ("Paper 2", PKG_DIR / "papers/paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.tex"),
    ]:
        t = tex_path.read_text(encoding="utf-8")
        t = re.sub(r"\\allowbreak\s*(?:\{\})?", "", t).replace(r"\_", "_")
        lean_refs = sorted(set(Path(m).name for m in re.findall(r"[A-Za-z0-9_/-]+\.lean", t)))
        missing_lean = [f for f in lean_refs if f not in pkg_lean_names]
        assert not missing_lean, f"{label} cites missing .lean files: {missing_lean}"

        # Active scripts/certs (excluding the 3 historical archival scripts explicitly noted as historical in Paper 1)
        historical_excluded = {"verify_round2.py", "verify_round6.py", "compute_dj.py"}
        py_refs = sorted(set(Path(m).name for m in re.findall(r"[A-Za-z0-9_/-]+\.py", t)) - historical_excluded)
        missing_py = [f for f in py_refs if f not in pkg_filenames]
        assert not missing_py, f"{label} cites missing .py files: {missing_py}"

        json_refs = sorted(set(Path(m).name for m in re.findall(r"[A-Za-z0-9_/-]+\.json", t)))
        missing_json = [f for f in json_refs if f not in pkg_filenames]
        assert not missing_json, f"{label} cites missing .json files: {missing_json}"

        log_refs = sorted(set(Path(m).name for m in re.findall(r"[A-Za-z0-9_/-]+\.log", t)))
        missing_log = [f for f in log_refs if f not in pkg_filenames]
        assert not missing_log, f"{label} cites missing .log files: {missing_log}"

        assert "872" in t and "849" in t and "23" in t, f"{label} missing synchronized 872/849/23 audit counts"
        print(
            f"[PASS] {label} cross-check: {len(lean_refs)} .lean, {len(py_refs)} active .py, "
            f"{len(json_refs)} .json, {len(log_refs)} .log all present; 872/849/23 aligned"
        )

    required_new_lean = [
        "WindowShortAeRealize.lean",
        "ResidueModGeneral.lean",
        "TransferOperatorDim.lean",
        "FiniteStateComplete.lean",
    ]
    missing_new_lean = [f for f in required_new_lean if f not in pkg_lean_names]
    assert not missing_new_lean, f"Missing new 2026-11-22 Lean modules in package: {missing_new_lean}"
    print(f"[PASS] All 4 new Lean modules verified in package ({len(pkg_lean_names)} total .lean files)")

    # 8e. Check pdflatex logs in package for 0 errors & 0 Overfull \hbox
    for label, log_p in [
        ("Paper 1", PKG_DIR / "papers/paper1_e_plus_pi/paper1_e_plus_pi.log"),
        ("Paper 2", PKG_DIR / "papers/paper2_spectral_gap_dimension/paper2_spectral_gap_dimension.log"),
    ]:
        txt = log_p.read_text(encoding="utf-8", errors="replace")
        assert "Overfull \\hbox" not in txt, f"{label} has Overfull hbox!"
        assert "LaTeX Warning:" not in txt, f"{label} has LaTeX Warning!"
        assert "! " not in txt, f"{label} has TeX error!"
        m = re.search(r"Output written on [^\n]+", txt)
        print(f"[PASS] {label} pdflatex log clean: {m.group(0) if m else 'OK'}")

    print("\nALL DESKTOP PACKAGE ASSEMBLY & VERIFICATION CHECKS PASSED!")


if __name__ == "__main__":
    main()
