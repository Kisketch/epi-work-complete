# Windows 下界组装与合入记录（2026-11-21）

> 一句总判断：paper2 §7 `thm:windows` 的计数核心已完整形式化——主定理 `coprime_count_ge`（`R ≥ 10^6 → R²/10000 ≤ copCount R`）及全部 31 个支撑声明 `lake env lean` EXIT 0、零 sorry；全量审计复跑 **531 条（499＋32），`sorryAx = 0`**，新增 32 条全部仅依赖 Lean 基础三公理。

## 一、文件清单（4 个，namespace 均为 `WindowMobiusCount`）

| 文件 | 内容 | 定理数 |
|---|---|---|
| `EpiFormal/WindowMobiusCount.lean` | §1–§5：box 定义、nat 除法、Möbius 示性、精确恒等式、实分析界（harmonic tail、tail_sq） | 13（审计打印） |
| `EpiFormal/WindowMobiusPartial.lean` | 子代理 A：first-five `539/900`、tail ≤ 1/5、partial ≥ 359/900（`1 ≤ D` 前提为真修正） | 3 |
| `EpiFormal/WindowWindowBounds.lean` | 子代理 B：W1/W2 ∈ [0.019R, 0.021R]、Acount/Bcount ±1 界＋2 辅助等式 | 8＋2 |
| `EpiFormal/WindowMainBound.lean` | 主线程 §5c：e³>10 → log10<3 → log(10⁶)<18 → logMhi 界 → 误差界 → 主组装 | 6 |

## 二、关键设计决策（可复查）

1. **Möbius 部分和下界 359/900**：前五项精确值 539/900（`decide`＋μ 值＋`norm_num`）减尾部上界 1/5；`D=0` 时原命题为假，加 `1 ≤ D` 前提（子代理 A 发现并修正，主定理处由 `Mlo ≥ 1` 满足）。
2. **窗口界 ±1 绝对形式**：`Acount_lo/hi` 给 `W1/d ∓ 1` 界，避免相对误差；组装时用 `add_div` 合并为 `(W1+W2)/d`。
3. **对数链避开 rpow**：用整数指数路线 `e³ > 10 → log 10 < 3 → log(10⁶) < 18`（`exp_nat_mul`/`log_pow`/`log_div`/`log_le_sub_one_of_pos` 均为现货引理，已逐条核名），不用任何 rpow 上界。
4. **终局余量**：`0.00014399889·R² − 1.116·R − 1.5e-8·R² ≥ R²/10000` 在 `R ≥ 30000` 成立（`nlinarith`＋`hC` 常数引理＋`(R−30000)*R ≥ 0` 乘积提示），阈值 10⁶ 处余量约 39×。
5. **技术债清理**：`abs_add` 在当前 mathlib 无此名，改用 `abs_le.mpr`＋`abs_mul` 桥接；`Finset.card_Icc` 实为 `Nat.card_Icc`；`log_lt_iff_lt_exp`（非 `log_lt_iff_exp_lt`）；`mul_lt_mul_of_pos_left`（严格版）。

## 三、构建与审计（命令原文）

- 单目标：`lake build EpiFormal.WindowMobiusPartial` / `WindowWindowBounds` / `WindowMainBound` 均 EXIT 0（9048–9050 jobs）。
- 全量：`lake build` EXIT 0（见 `verification/window_wired_build_20261121.log`）。
- 审计：`lake env lean Audit.lean` EXIT 0，输出 `verification/audit_window_wired_20261121.log`：
  - **总数 531 = 499（旧）＋ 32（新）**；`sorryAx` 命中 0；error 行 0。
  - 签名分布：485× 基础三公理（两种空格排版）＋ 20× `[propext, Quot.sound]` ＋ 22× 含经典白名单（`e/pi_transcendental`、`mu_e_eq_two` 及其组合）＋ 2× 仅 `propext` ＋ 1× 零公理。
  - 32 条 `WindowMobiusCount.*` 条目逐条核验：全部落在基础三公理组，无白名单、无自加。
- 接线（三处清单）：`EpiFormal.lean` ＋4 imports；`Audit.lean` ＋4 imports、＋32 `#print`（分四节注释）。

## 四、诚实口径

- 类别：第 5 类（文献核查与复现）＋形式化引理 [1]（计数恒等式与显式常数界，无新数学定理声称）。
- `thm:windows` 的 Frostman 质量分布组装（dim ≥ b/2）与连分数圆柱基础设施**仍为纸面**，本文件只交付其消耗的 `≫ R²` 计数输入（docstring 已明确声明接口边界）。
- `e+π` 无理性仍开放，与本文无关（基线不变）。

## 五、后续队列

no-short-dim（设计文档 `verification/windows_noshortdim_design_20261121.md` 已备，L01–L20 引理表；圆柱基础设施为单点阻塞）→ residues Bowen 组装。
