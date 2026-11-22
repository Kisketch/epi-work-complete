#!/usr/bin/env bash
set -u
echo "== CACHE CLEAN =="
rm -rf "$HOME/.config/Claude/Cache" "$HOME/.config/Claude/Local Storage" \
       "$HOME/.config/Claude/IndexedDB" "$HOME/.config/Claude/logs" \
       "$HOME/.config/Claude/scratch-workspaces" "$HOME/.config/Claude/git-shadow" \
       "$HOME/.config/Claude/claude-code-sessions" \
       "$HOME/.config/claude-cage/editor-workspace"
printf '{}\n' > "$HOME/.config/Ultralytics/settings.json"
echo "== RESCAN =="
grep -rl "Lgnatius\|Kisketch\|2300495663" "$HOME/.gitconfig" "$HOME/.config" "$HOME/.ssh" "$HOME/.profile" "$HOME/.bashrc" "$HOME/.zshenv" "$HOME/.zshrc" 2>/dev/null || echo NO_REAL_IDENTITY_IN_CONFIG
echo "== SETUP LOG =="
tail -6 "$HOME/epi_setup.log"
echo "== CACHE CLEAN DONE =="
