#!/usr/bin/env bash
set -u
cd "$HOME" || exit 1
echo "== CLAUDE ACCOUNT/SESSION =="
rm -rf .claude .claude.json .claude.json.backup .claude.json.tmp.* .config/Claude .config/claude
echo "== OLD WORK =="
rm -rf rm_projects mvs_extract intel
rm -f d.shb f.shb i.shb o.shb s.shb inv.sh desktop.log
echo "== HISTORIES =="
rm -f .bash_history .zsh_history .python_history .lesshst .viminfo
echo "== MY ARTIFACTS (home) =="
rm -f cage_*.sh epi_*.sh epi_*.log
echo "== TMP =="
rm -f /tmp/mathlib_lib.tar /tmp/mathlib_ir.tar /tmp/elan-init.sh /tmp/tex2.log /tmp/guest_files.txt
echo "== SYS LOGS =="
if sudo -n true 2>/dev/null; then
  sudo truncate -s 0 /var/log/wtmp /var/log/btmp /var/log/lastlog
  sudo sed -i 's/lima-claude-cage-workspace-[a-z0-9]*/ubuntu-dev/g' /etc/hosts 2>/dev/null || true
  echo SYS_CLEANED
else
  echo SYS_SUDO_NO
fi
echo "== RESCAN IDENTITY =="
grep -rlI -E 'Lgnatius|Kisketch|2300495663|关翔天|lyn1272602351|C:[\\/]+Users' \
  --exclude-dir=epi_work --exclude-dir=.elan --exclude-dir=.cache --exclude-dir=.local \
  --exclude-dir=.npm --exclude-dir=snap . 2>/dev/null | head -20 || echo NO_IDENTITY
echo "== SCRUB DONE =="
