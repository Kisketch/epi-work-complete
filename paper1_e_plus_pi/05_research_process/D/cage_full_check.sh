#!/usr/bin/env bash
set -u
pkill -9 -f 'bin/lean' 2>/dev/null || true
cd "$HOME/epi_work" || exit 1
echo "== FILE LISTS =="
find . -path './epi_formal/.lake' -prune -o -type f -print | sort > /tmp/guest_files.txt
wc -l < /tmp/guest_files.txt
echo "== CRLF CHECK (text files) =="
crlf=0
while IFS= read -r f; do
  case "$f" in
    *.lean|*.tex|*.md|*.toml|*.json|*.sh|*.txt)
      if head -c 2000 "$f" | grep -q $'\r'; then crlf=$((crlf+1)); echo "CRLF: $f"; fi ;;
  esac
done < /tmp/guest_files.txt
echo "CRLF_COUNT=$crlf"
echo "== GIT DIRS =="
find . -name '.git' -maxdepth 4 2>/dev/null || true
echo "== TOOLCHAIN =="
"$HOME/.elan/bin/lean" --version
"$HOME/.elan/bin/lake" --version
echo "== TEX =="
pdflatex --version | head -1
echo "== PY =="
python3 --version
echo "== PDF =="
ls -la ./*_e_plus_pi/*.pdf 2>/dev/null | head -4
echo "== OLEAN COUNTS =="
echo "mathlib: $(find ./epi_formal/.lake/packages/mathlib/.lake/build/lib -name '*.olean' 2>/dev/null | wc -l)"
echo "project: $(find ./epi_formal/.lake/build/lib -name '*.olean' 2>/dev/null | wc -l)"
echo "== FULL CHECK DONE =="
