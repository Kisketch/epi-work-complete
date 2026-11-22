# affine-window phase-1 合入记录（2026-11-21）

> 一句总判断：`AffineWindowAssembly.lean`（7 声明，namespace AffineWindow，主会话亲手写+复验）已合入，全量审计 **489 条（482+7）、`sorryAx = 0`**；论文一 triage #2（explicit-period + affine-window 组装）转正为"组装已核实/实例化接口纸面"。

## 一、复验（主会话亲手，含两次环境级误报的排除）

- 文件 5.4KB，UTF-8 无 BOM（头字节 `69 6D 70`），`^axiom` 零声明，`sorry` 1 命中 = 第 57 行中文注释（复验确认非代码）。
- 弯路 1：`Select-Object -First` 截断长输出管道杀死 lean 写端致 EXIT=-1（教训重现，复验一律落盘）。
- 弯路 2：`variable` 假说绑定在此环境行为异常（`B c` 注册而 `hB hc` 报 unknown，证据矛盾），对照 Trichotomy（全显式、零 variable）后改全显式绑定，一次通过。
- 弯路 3：`first_digit_shift` 末 `ring` 报 No goals（`field_simp` 已闭合），删之。
- `lake env lean` EXIT 0（`affine_verify7_20261121.log`）：7/7 公理清单——T_pos/D_pos/first_digit_shift 纯基础三公理；r_ge_three 仅 `[propext, Quot.sound]`；D_period 仅 `[propext]`；r_period 零公理。

## 二、合入与审计

- `EpiFormal.lean` +1 import；`Audit.lean` +1 import + 7 条 `#print`。
- 单目标构建 EXIT 0；全量审计 `audit_affine_wired_20261121.log` EXIT 0：489 条，`sorryAx` 0，error 0，AffineWindow 7 条全在。
- 白名单总数不变（新增 7 条零白名单、零项目自加）。

## 三、口径

- 转正的是纸面 §3 代数组装（content/divisibility/偶性/r 奇≥3/周期传递/首位增量代数）；接口假设显式（locked denominators / Hermite recurrence / mod-T congruence / digit rule）。
- 仍纸面：窗口长度 `r_j` 的完整组装（Hermite 递推实例化）、mod-T 二项同余的 Lean 证明、首位增量的 `F_{j-1}` 递归闭合——属 phase-2。
