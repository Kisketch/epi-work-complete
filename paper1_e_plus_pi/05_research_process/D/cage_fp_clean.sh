#!/usr/bin/env bash
set -u
echo "== GIT NEUTRAL =="
git config --global user.name "cage"
git config --global user.email "cage@localhost"
git config --global --unset-all credential.https://github.com.helper || true
git config --global --unset-all credential.https://gist.github.com.helper || true
cat "$HOME/.gitconfig"
echo "== GH LOGOUT =="
gh auth logout --hostname github.com 2>&1 || true
rm -f "$HOME/.config/gh/hosts.yml"
gh auth status 2>&1 | head -3 || true
echo "== HOSTNAME =="
if sudo -n true 2>/dev/null; then
  sudo hostnamectl set-hostname ubuntu-dev
  echo "hostname now: $(hostname)"
else
  echo "SUDO_NEEDS_PASSWORD: hostname left as $(hostname)"
fi
echo "== FP CLEAN DONE =="
