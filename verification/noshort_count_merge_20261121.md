# no-short-dim L06 合入记录（2026-11-21）

> 一句总判断：no-short-dim 计数核心 21 条 S 定理全部合入主树审计，全量 560 条（539+21），`sorryAx = 0`，21 条全部仅依赖 Lean 基础三公理——L06 转正。

## 一、交付物

- 源文件：`epi_formal/EpiFormal/NoShortDimCount.lean`（671 行，`namespace NoShortDim`，21 定理：boxS×5、W×7、AcountS×2、BcountS×2、keyS、prodS、coprimeS_count_eq、logMhiS_le、errS_bound、coprimeS_count_ge）。
- 接线：`EpiFormal.lean` +1 import；`Audit.lean` +1 import +21 prints。
- 审计日志：`verification/audit_noshort_count_wired_20261121.log`（EXIT 0，560 条，sorryAx 0，error 0）。

## 二、修复链（本轮三个坑）

1. **缺 import WindowMainBound**：`log106_lt` 引用报未知标识符，错误恢复注入 sorryAx（文件无 sorry 文本）。补 import 后单文件零错误。
2. **缺 `end NoShortDim`**：命名空间未闭合（linter 警告）。已补。
3. **print 名与实际声明不符**：初版 6 条用无 S 名（约定文档 aspirational 名），实际 21 定理全 S 后缀。探针（无 BOM 写法）确认 olean 不可解析无 S 名后，按实际名重写 21 条。另发现 olean 缺失曾致未知常量：L06 初版只跑单文件检查、漏单目标构建——接线清单增补为"源文件/import×2/prints/**olean 落盘**"五项。

## 三、公理分布

- 21/21 = `[propext, Classical.choice, Quot.sound]`，白名单零新增（项目白名单总数仍 22，见 take-over 后基线）。
- 全量 560 = 539（ratio 合入后）+ 21。

## 四、诚实口径

- L06（计数恒等式+矩形下界+误差传递）转正；组装（tower/Markov/BC/Frostman）仍纸面，属下一阶段。
- `coprimeS_count_ge` 的 R≥3000 系数 0.0009 仍保守（window 版 R≥30000 余量 39×），统一收紧留待组装阶段。
- e+π 无理性基线不变。
