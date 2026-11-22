#!/usr/bin/env bash
set -u
pkill -f 'cage_verify2.sh' || true
pkill -f 'lake' || true
pkill -f 'lean --' || true
sleep 1
echo "== REMAIN =="
pgrep -af 'lake|lean' || echo NONE
echo "== GUEST CACHE FILES =="
ls "$HOME/epi_work/epi_formal/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Nat/" 2>/dev/null | grep -i gcd | head
echo "== STOP BUILD DONE =="
