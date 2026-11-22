#!/usr/bin/env bash
set -u
pkill -f 'epi_setup.sh' || true
pkill -f 'lake exe cache' || true
pkill -f 'Cache.Main' || true
pkill -f 'cache get' || true
sleep 1
echo "== REMAIN =="
pgrep -af 'epi_setup|Cache.Main|lake' || echo NONE
echo "== STOP DONE =="
