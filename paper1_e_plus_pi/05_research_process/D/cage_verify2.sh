#!/usr/bin/env bash
set -u
exec > "$HOME/epi_verify2.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME/epi_work/epi_formal"
echo "== BUILD PROJECT LIB =="
lake build
echo "BUILD_EXIT=$?"
echo "== VERIFY PROP81 =="
lake env lean "$HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean"
echo "VERIFY_EXIT=$?"
echo "== VERIFY2 DONE =="
