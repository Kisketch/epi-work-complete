#!/usr/bin/env bash
set -u
pkill -9 -f 'lake' || true
pkill -9 -f 'bin/lean' || true
sleep 2
echo "== REMAIN =="
pgrep -af 'lake|bin/lean' || echo NONE
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME/epi_work/epi_formal"
setsid bash -c 'export PATH=$HOME/.elan/bin:$PATH; cd $HOME/epi_work/epi_formal; { echo "== CLEAN BUILD =="; lake build +EpiFormal.EulerConvergents:olean; echo MOD_EXIT=$?; lake env lean $HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean; echo VERIFY_EXIT=$?; echo CLEAN_BUILD_DONE; } > $HOME/epi_clean_build.log 2>&1' </dev/null >/dev/null 2>&1 &
echo CLEAN_LAUNCHED
