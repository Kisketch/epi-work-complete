#!/usr/bin/env bash
set -u
echo "== COMPILING =="
pgrep -af 'bin/lean' | grep -oE 'EpiFormal/[A-Za-z]+\.lean' | sort | uniq -c
echo "== LOG TAIL =="
tail -4 "$HOME/epi_mod_bg.log"
echo "== PS DONE =="
