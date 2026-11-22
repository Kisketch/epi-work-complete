#!/usr/bin/env bash
set -u
exec > "$HOME/epi_tex.log" 2>&1
cd "$HOME/epi_work"/*_e_plus_pi || exit 1
echo "== PDFLATEX =="
pdflatex -interaction=nonstopmode -halt-on-error 第一阶段_e_plus_pi.tex > /dev/null 2>&1
pdflatex -interaction=nonstopmode -halt-on-error 第一阶段_e_plus_pi.tex > /tmp/tex2.log 2>&1
echo "TEX_EXIT=$?"
tail -5 /tmp/tex2.log
ls -la 第一阶段_e_plus_pi.pdf
echo "== TEX DONE =="
