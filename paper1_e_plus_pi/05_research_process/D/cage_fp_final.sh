#!/usr/bin/env bash
set -u
echo "== MACHINEID =="
if sudo -n true 2>/dev/null; then
  sudo rm -f /etc/machine-id
  sudo systemd-machine-id-setup
  echo "machine-id now: $(cat /etc/machine-id)"
else
  echo "SUDO_NEEDS_PASSWORD"
fi
echo "== CONFIG SCAN =="
grep -rl "Lgnatius\|Kisketch\|2300495663" "$HOME/.gitconfig" "$HOME/.config" "$HOME/.ssh" "$HOME/.profile" "$HOME/.bashrc" "$HOME/.zshenv" "$HOME/.zshrc" 2>/dev/null || echo NO_REAL_IDENTITY_IN_CONFIG
echo "== FP FINAL DONE =="
