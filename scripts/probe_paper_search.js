// 诊断脚本：对比 paper-search MCP 两种命令形态能否完成 MCP initialize + tools/list
// 用途：确认项目 opencode.json 中 "uvx paper-search-mcp"（用户原文，无钉版）与
//       "uvx --with mcp<2 paper-search-mcp"（全局配置已验证形态）的启动差异，留下可复查证据。
// 运行：node scripts/probe_paper_search.js
const { spawn } = require("node:child_process");
const readline = require("node:readline");
const fs = require("node:fs");
const ROOT = "C:\\Users\\Lgnatius\\Documents\\qwen-agent\\QOTCWZPRRA\\default\\epi_work";

async function probe(label, args) {
  return new Promise((resolve) => {
    const proc = spawn("uvx", args, { cwd: ROOT, shell: false });
    const out = { label, command: ["uvx", ...args] };
    const pending = new Map();
    let nextId = 1;
    let stderrTail = "";

    proc.stderr.setEncoding("utf8");
    proc.stderr.on("data", (d) => { stderrTail = (stderrTail + d).slice(-4000); });
    proc.on("exit", (code, signal) => {
      out.exited = { code, signal };
      for (const [, res] of pending) {
        res({ error: { code: -32000, message: `connection closed before response (exit code=${code}, signal=${signal})` } });
      }
      pending.clear();
    });

    const rl = readline.createInterface({ input: proc.stdout });
    rl.on("line", (line) => {
      line = line.trim();
      if (!line) return;
      try {
        const msg = JSON.parse(line);
        if (msg.id !== undefined && pending.has(msg.id)) {
          pending.get(msg.id)(msg);
          pending.delete(msg.id);
        }
      } catch { /* non-JSON line, ignore */ }
    });

    const call = (method, params) => new Promise((res) => {
      const id = nextId++;
      pending.set(id, res);
      proc.stdin.write(JSON.stringify({ jsonrpc: "2.0", id, method, params }) + "\n");
      setTimeout(() => {
        if (pending.has(id)) {
          pending.delete(id);
          res({ error: { code: -32001, message: "timeout waiting for " + method } });
        }
      }, 45000);
    });

    const finish = () => { try { proc.kill(); } catch {} resolve(out); };
    const hardTimeout = setTimeout(() => { out.failure = "overall timeout (120s)"; finish(); }, 120000);

    (async () => {
      try {
        const init = await call("initialize", {
          protocolVersion: "2024-11-05",
          capabilities: {},
          clientInfo: { name: "probe_paper_search", version: "0.1" },
        });
        if (init.error) {
          out.initialize = { error: init.error };
          out.failure = "initialize rejected: " + JSON.stringify(init.error);
        } else {
          out.initialize = { serverInfo: init.result.serverInfo, protocolVersion: init.result.protocolVersion };
          proc.stdin.write(JSON.stringify({ jsonrpc: "2.0", method: "notifications/initialized" }) + "\n");
          const tl = await call("tools/list", {});
          if (tl.error) {
            out.tools = { error: tl.error };
            out.failure = "tools/list rejected: " + JSON.stringify(tl.error);
          } else {
            out.tools = { count: tl.result.tools.length, names: tl.result.tools.map((t) => t.name) };
          }
        }
      } catch (e) {
        out.failure = String(e);
      }
      out.stderrTail = stderrTail.slice(-2000);
      clearTimeout(hardTimeout);
      finish();
    })();
  });
}

(async () => {
  const verbatim = await probe("verbatim-user-spec", ["paper-search-mcp"]);
  const pinned = await probe("pinned-mcp-lt-2", ["--with", "mcp<2", "paper-search-mcp"]);
  const report = JSON.stringify(
    { timestamp: new Date().toISOString(), prober: "scripts/probe_paper_search.js", verbatim, pinned },
    null,
    2
  );
  fs.writeFileSync(ROOT + "\\scripts\\probe_paper_search_output.json", report, "utf8");
  console.log(report);
})();
