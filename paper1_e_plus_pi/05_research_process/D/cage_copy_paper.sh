#!/usr/bin/env bash
set -u
exec >> "$HOME/epi_setup.log" 2>&1
echo "== COPY PAPER FIX =="
src=$(echo /c/Users/Lgnatius/.claude-cage-downloads/epi_staging/*_e_plus_pi)
echo "src=$src"
cp -a "$src" "$HOME/epi_work/"
dst=$(echo "$HOME/epi_work"/*_e_plus_pi)
echo "paper files: $(find "$dst" -type f | wc -l)"
echo "formal files: $(find "$HOME/epi_work/epi_formal" -type f | wc -l)"
echo "== COPY FIX DONE =="
