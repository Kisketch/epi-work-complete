# 串行构建全部 132 模块（避开 Windows 并发 .olean 锁抖动；lake 本版本无 -j 选项）
# 用法：在 epi_formal 目录下 py -3.13 ../scripts_lake_serial.py（或直接 lake env 下运行）
# 输出：verification/lake_serial_build.log
import re
import subprocess
import os

os.chdir(r"C:\Users\Lgnatius\.local\share\opencode\worktree\9811dd\proud-panda\epi_formal")
mods = []
for line in open("EpiFormal.lean", encoding="utf-8"):
    line = line.strip()
    if line.startswith("import EpiFormal."):
        mods.append(line.split("import ")[1].strip())

log = open(r"C:\Users\Lgnatius\.local\share\opencode\worktree\9811dd\proud-panda\verification\lake_serial_build.log",
           "w", encoding="utf-8")
ok, fail = 0, []
for m in mods:
    r = subprocess.run(["lake", "build", m], capture_output=True, text=True, errors="replace")
    status = "OK" if r.returncode == 0 else "FAIL"
    log.write(f"{status} {m}\n")
    if r.returncode != 0:
        fail.append(m)
        tail = (r.stdout + r.stderr)[-800:]
        log.write(tail + "\n")
    else:
        ok += 1
    log.flush()
    print(f"{status} {m}", flush=True)
log.write(f"\nDONE ok={ok} fail={len(fail)}\n")
for m in fail:
    log.write(f"FAILED {m}\n")
print(f"DONE ok={ok} fail={len(fail)}")
