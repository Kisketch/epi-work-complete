#!/usr/bin/env bash
set -u
echo "== PKG LOG =="
sed -n '/== PACKAGES ==/,$p' "$HOME/epi_setup.log" | head -50
echo "== PROCS =="
pgrep -af 'lake|git-remote|git fetch' | head -6
echo "== PKG DIR =="
ls "$HOME/epi_work/epi_formal/.lake/packages" 2>/dev/null || echo NO_PACKAGES
echo "== DIAG2 DONE =="
