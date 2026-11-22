# papers/ — arxiv MCP 文献落盘目录

- **用途**：opencode.json 中 `arxiv` MCP（`uvx arxiv-mcp-server --storage-path ./papers`）的默认下载目录；`paper-search` MCP 的 `download_*` 系列工具也可使用 `./papers` 作为 `save_path`。
- **历史**：本目录原为工作区论文同步副本目录，2026-11-21 重组时其内容已全部归档、目录一度被移除；因 arxiv MCP 配置仍指向 `./papers`，当日重建为空目录。
  - 旧论文一同步副本（原 `papers/第一阶段_e_plus_pi.tex/.pdf`）→ `paper1_e_plus_pi/06_historical_versions/archive_snapshots/papers_old/paper1_old.tex/.pdf`
  - 旧论文二同步副本（原 `papers/第二阶段_谱隙与维数.tex/.pdf`）→ `paper2_spectral_gap_dimension/historical_versions/paper2_old.tex/.pdf`
- 新下载的文献 PDF 请直接落在本目录，引用核查留痕按 `verification/` 既有格式另建记录。
