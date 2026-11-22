#!/usr/bin/env bash
set -u
echo "== GITCONFIG =="
cat "$HOME/.gitconfig" 2>/dev/null
echo "== GH =="
command -v gh && gh auth status 2>&1 | head -5
ls "$HOME/.config/gh" 2>/dev/null
echo "== SSH DIR =="
ls -la "$HOME/.ssh" 2>/dev/null
echo "== HOSTNAME =="
hostname
cat /etc/hostname
echo "== MACHINEID =="
cat /etc/machine-id
echo "== TIMEZONE =="
cat /etc/timezone 2>/dev/null
readlink -f /etc/localtime
echo "== LOCALE =="
locale | head -3
echo "== GH CONFIG CONTENT =="
cat "$HOME/.config/gh/hosts.yml" 2>/dev/null | sed 's/oauth_token:.*/oauth_token: <REDACTED>/'
echo "== CLAUDE GIT =="
grep -l -r "Lgnatius\|关翔天\|2300495663" "$HOME/.gitconfig" "$HOME/.config/gh" "$HOME/.ssh" 2>/dev/null
echo "== FP INVENTORY DONE =="
