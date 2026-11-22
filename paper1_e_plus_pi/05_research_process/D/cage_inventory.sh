#!/usr/bin/env bash
set -u
echo "== OS =="
head -3 /etc/os-release
echo "== HOME =="
ls -la "$HOME"
echo "== TOOLS =="
for c in git python3 pip3 pdflatex xelatex latexmk lean lake elan gcc g++ make cmake curl wget rsync tar unzip; do
  printf '%s: ' "$c"
  command -v "$c" || echo MISSING
done
echo "== PYTHON PKGS =="
python3 -c "import sympy, mpmath, numpy; print('sympy', sympy.__version__, 'mpmath', mpmath.__version__, 'numpy', numpy.__version__)" 2>&1 | head -2
echo "== MOUNTS =="
mount | grep -Ei 'sshfs|9p|virtiofs' || echo NO_SHARE_MOUNT
echo "== DISK =="
df -h / | tail -1
echo "== MEM =="
free -h | head -2
echo "== NET =="
env | grep -i proxy || echo NO_PROXY_ENV
echo "== EXISTING EPI =="
ls -d "$HOME"/epi* "$HOME"/*epi* 2>/dev/null || echo NONE
echo "== DONE =="
