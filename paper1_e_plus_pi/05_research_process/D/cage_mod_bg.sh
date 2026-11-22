#!/usr/bin/env bash
set -u
pkill -f 'lake build' || true
pkill -f 'cage_mod_verify.sh' || true
sleep 2
pgrep -af 'lake' || echo NO_LAKE
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME/epi_work/epi_formal"
setsid bash -c 'export PATH=$HOME/.elan/bin:$PATH; cd $HOME/epi_work/epi_formal; { echo "== MOD BG =="; lake build +EpiFormal.EulerConvergents:olean; echo MOD_EXIT=$?; lake env lean $HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean; echo VERIFY_EXIT=$?; echo MOD_BG_DONE; } > $HOME/epi_mod_bg.log 2>&1' </dev/null >/dev/null 2>&1 &
echo BG_LAUNCHED
