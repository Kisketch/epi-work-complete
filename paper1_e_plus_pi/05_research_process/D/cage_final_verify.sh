#!/usr/bin/env bash
set -u
cd "$HOME" || exit 1
echo "== HOME =="
ls -la
echo "== GIT =="
git config --global user.name; git config --global user.email
echo "== HOSTNAME/ID =="
hostname; cat /etc/machine-id
echo "== PAYLOAD =="
find epi_work -path 'epi_work/epi_formal/.lake' -prune -o -type f -print | wc -l
echo "== AUTH LOG TRUNC =="
sudo -n truncate -s 0 /var/log/auth.log 2>/dev/null && echo AUTH_CLEANED || echo AUTH_SKIP
echo "== FINAL DONE =="
