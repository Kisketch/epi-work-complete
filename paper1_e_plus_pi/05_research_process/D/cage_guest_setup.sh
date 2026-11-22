#!/usr/bin/env bash
set -u
exec > "$HOME/epi_setup.log" 2>&1
echo "== COPY =="
mkdir -p "$HOME/epi_work"
cp -a "/c/Users/Lgnatius/.claude-cage-downloads/epi_staging/." "$HOME/epi_work/"
echo "paper files: $(find "$HOME/epi_work/论文一_e_plus_pi" -type f | wc -l)"
echo "formal files: $(find "$HOME/epi_work/epi_formal" -type f | wc -l)"
echo "== ELAN =="
export PATH="$HOME/.elan/bin:$PATH"
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
elan --version
elan toolchain install leanprover/lean4:v4.35.0
cd "$HOME/epi_work/epi_formal"
echo "== TOOLCHAIN =="
lean --version
lake --version
echo "== PACKAGES =="
lake update
echo "== CACHE =="
lake exe cache get
echo "== VERIFY COMPILE =="
lake env lean "$HOME/epi_work/论文一_e_plus_pi/parallel_work/D/Prop81.lean"
echo "VERIFY_EXIT=$?"
echo "== PATH PERSIST =="
grep -q '.elan/bin' "$HOME/.bashrc" || sed -i '1i export PATH="$HOME/.elan/bin:$PATH"' "$HOME/.bashrc"
grep -q '.elan/bin' "$HOME/.zshenv" || printf 'export PATH="$HOME/.elan/bin:$PATH"\n' >> "$HOME/.zshenv"
echo "== SETUP DONE =="
