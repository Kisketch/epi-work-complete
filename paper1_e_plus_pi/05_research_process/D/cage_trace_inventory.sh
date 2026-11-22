#!/usr/bin/env bash
set -u
cd "$HOME" || exit 1
echo "== IDENTITY MATCHES (home, excl payload/toolchain) =="
grep -rlI -E 'Lgnatius|Kisketch|2300495663|关翔天|lyn1272602351|C:[\\/]+Users' \
  --exclude-dir=epi_work --exclude-dir=.elan --exclude-dir=.cache --exclude-dir=.local \
  --exclude-dir=.npm --exclude-dir=snap . 2>/dev/null | head -60
echo "== HISTORIES =="
ls -la .bash_history .zsh_history .python_history .lesshst .viminfo 2>/dev/null
echo "== OLD WORK =="
du -sh rm_projects mvs_extract intel 2>/dev/null
ls -la *.shb inv.sh desktop.log 2>/dev/null
echo "== CLAUDE =="
du -sh .claude .claude.json .config/Claude .config/claude 2>/dev/null
echo "== MY ARTIFACTS =="
ls -la cage_*.sh epi_*.sh epi_*.log 2>/dev/null | head -30
ls -la /tmp/mathlib_*.tar /tmp/elan-init.sh /tmp/tex2.log /tmp/guest_files.txt 2>/dev/null
echo "== SYS LOGS =="
ls -la /var/log/wtmp /var/log/btmp /var/log/lastlog 2>/dev/null
grep -l 'lima-claude-cage' /etc/hosts /etc/hostname 2>/dev/null
echo "== INV DONE =="
