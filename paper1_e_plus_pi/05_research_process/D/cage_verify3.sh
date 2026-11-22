#!/usr/bin/env bash
set -u
exec > "$HOME/epi_verify3.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"
IR="$HOME/epi_work/epi_formal/.lake/packages/mathlib/.lake/build/ir"
mkdir -p "$IR"
tar -xf /tmp/mathlib_ir.tar -C "$IR"
echo "ir files: $(find "$IR" -type f | wc -l)"
cd "$HOME/epi_work/epi_formal"
echo "== BUILD =="
lake build
echo "BUILD_EXIT=$?"
echo "== VERIFY PROP81 =="
lake env lean "$HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean"
echo "VERIFY_EXIT=$?"
echo "== VERIFY3 DONE =="
