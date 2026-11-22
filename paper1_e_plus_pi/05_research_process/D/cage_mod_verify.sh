#!/usr/bin/env bash
set -u
exec > "$HOME/epi_mod_verify.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME/epi_work/epi_formal"
echo "== BUILD MODULE OLEAN =="
lake build +EpiFormal.EulerConvergents:olean
echo "MOD_BUILD_EXIT=$?"
echo "== ENV VERIFY PROP81 =="
lake env lean "$HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean"
echo "VERIFY_EXIT=$?"
echo "== MOD VERIFY DONE =="
