# E2 ρ封顶 + htop前提手术合入记录（2026-11-21）

## 一句总判断

`WindowFrostmanDirect.lean` ρ封顶与 Hwin `htop` 前提手术完成：单文件 EXIT 0 零输出、单目标构建 EXIT 0、全量审计 **646 条（零新增 prints，文件↔日志双向全唯一），`sorryAx = 0`**。

## 改动（5 处）

1. `ρ i` 加 `min (r0R / 2)` 封顶（镜像模板 L953）。
2. `hρ_pos` 改 `lt_min` 证明；`h2ρ_rpow` 改 `min_le_right` 链（原直接展开失效）。
3. 新增 `hV_ediam_le`（`direct_ediam_thickening_le` 本地引理 + `hcap` + `hd'` 经 `hr0def` + `add_le_add`）与 `hV_diam_le`（`toReal_mono` 断言在前 + `toReal_add/ofReal_ne_top/toReal_ofReal` + `linarith`；教训：`rw` 默认重写全部匹配，删重复 `toReal_ofReal`）。
4. Hwin 加 `(htop : ∀ i, Metric.diam (V i) ≤ 2 * r0R)` 前提（E2 侧可供给：`hV_diam_le`）。
5. 调用处传参加 `hFne` + `htop` 证明（顺序曾传反，已按 Hwin 签名顺序修正）。

## 动因（R3 补完）

- 无封顶时 S3 加厚集直径无上界（`2ρ` 可达 O(1)），discharge 的 F3a 选层（需 `diam ≤ top`）不可用。
- 封顶后 `diam(V i) ≤ 2·r0R` 一致成立；用方取 `r0R ≤ top/2` 即 discharge F3a。
- `hpos`（非空→直径为正）不受影响；S8a/S8c 的 `(2ρ)^s` 链经 `min_le_right` 保持。

## 验证

- 单文件两轮验证（终轮 EXIT 0 零输出）；单目标构建 EXIT 0（9049 jobs）；全量审计 `audit_frostdirect_htop_wired_20261121.log` EXIT 0，646 条。
