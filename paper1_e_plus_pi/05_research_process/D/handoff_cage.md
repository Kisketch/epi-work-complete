# Cage 部署交接（论文拷贝 + Linux 工具 + 去指纹）

日期：2026-11-19。Cage = 本机 Claude-Cage 隔离环境（Lima/QEMU，Ubuntu 22.04，用户 cage）。

## 一、论文拷贝（已完成，guest 本地磁盘，非共享挂载）

- 目标：`/home/cage/epi_work/论文一_e_plus_pi/`（37 文件，与源逐一对应，中文文件名完好）
- 同拷：`/home/cage/epi_work/epi_formal/`（74 个非缓存文件：lakefile、lean-toolchain、
  lake-manifest.json、EpiFormal 全部模块、各阶段 .lean/.tex 等）
- **排除** `.lake`（7.3GB/14.6万小文件）：在 guest 内用官方源重建（见下），避免 scp 海量小文件。
- 源未改动；宿主暂存 `C:\Users\Lgnatius\.claude-cage-downloads\epi_staging\` 留有副本（可删）。

## 二、Linux 完整工具（guest 内）

已有：git、python3+sympy/mpmath/numpy、pdflatex/xelatex（TeX Live）、gcc/g++/make/cmake、curl/wget/rsync。
新装：elan 4.4.0 + leanprover/lean4:v4.35.0（与主稿 pin 一致）；
`lake update` 按 lake-manifest.json 拉取 mathlib v4.35.0 rev 56a00585 及全部依赖；
`lake exe cache get` 下载官方 olean 缓存；随后 `lake env lean …/parallel_work/D/Prop81.lean` 验证。
PATH 持久化：.bashrc 首行 + .zshenv 均加 `$HOME/.elan/bin`。
安装日志：guest `~/epi_setup.log`（后台 setsid 运行，含 VERIFY_EXIT 与 SETUP DONE 标记）。

## 三、去指纹（已完成项）

| 项 | 原值 | 现值 |
|----|------|------|
| git user.name/email | Kisketch / 2300495663@qq.com | cage / cage@localhost |
| git credential helper | gh（指向真实账号） | 已移除 |
| gh 登录 | Kisketch + oauth token | 已 logout，hosts.yml 删除 |
| hostname | lima-claude-cage-workspace-64c7be0e | ubuntu-dev |
| /etc/machine-id | 329ff64e… | 随机重生成 c1fa7cc9… |
| 时区/语言 | （Cage 已伪装） | America/Vancouver / en_CA.UTF-8 保持 |
| 旧会话缓存 | Claude Desktop 缓存/scratch/git-shadow 含真实宿主路径 | 已清除（登录态保留） |
| Ultralytics settings | 含真实路径 | 重置为 {} |

配置层复扫：`NO_REAL_IDENTITY_IN_CONFIG`。
**未动**：Claude 登录态（.claude.json，用户账号 Pomni-ai）、Cage 应用自身配置、
宿主共享挂载里用户既有项目（rm_projects 等，非论文内容，未拷贝也未清理）。
**说明**：guest 内 `~/rm_projects`、`.bash_history` 等旧工作残留含用户既往项目痕迹，
属用户数据，未擅自删除；如需彻底无痕可另行确认后清理。

## 四、验证状态

- 拷贝：文件数核对 37/74，中文文件名 ls 确认完好。
- 工具链：lean --version / lake --version 输出 4.35.0 已确认。
- 依赖+缓存+编译：后台进行中，以 ~/epi_setup.log 的 `VERIFY_EXIT=0` 与 `SETUP DONE` 为准。
- 去指纹：gitconfig/gh/hostname/machine-id/配置复扫 均已读回确认。

## 五、复跑/接管

```
ssh -F D:\ClaudeCageData\state\lima\claude-cage-workspace-64c7be0e\ssh.config lima-claude-cage-workspace-64c7be0e
# guest 内：
bash -lc 'cd ~/epi_work/epi_formal && lake env lean ~/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean'
```
注意：guest 默认 shell 为 zsh，`==X==` 会触发 equals 展开；复杂命令写 .sh 用 bash 执行。
管道传中文脚本会乱码，用 scp 传文件再 bash。
