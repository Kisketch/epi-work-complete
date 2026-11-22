#!/usr/bin/env bash
set -u
exec > "$HOME/epi_verify.log" 2>&1
export PATH="$HOME/.elan/bin:$PATH"
echo "== EXTRACT MATHLIB CACHE =="
ML="$HOME/epi_work/epi_formal/.lake/packages/mathlib/.lake/build/lib"
mkdir -p "$ML"
tar -xf /tmp/mathlib_lib.tar -C "$ML"
echo "mathlib olean: $(find "$ML" -name '*.olean' | wc -l)"
echo "== BUILD DEPS =="
cd "$HOME/epi_work/epi_formal"
lake build batteries aesop Qq Cli proofwidgets importGraph LeanSearchClient plausible
echo "BUILD_DEPS_EXIT=$?"
echo "== VERIFY PROP81 =="
lake env lean "$HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean"
echo "VERIFY_EXIT=$?"
echo "== VERIFY DONE =="
