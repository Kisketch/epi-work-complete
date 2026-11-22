#!/usr/bin/env bash
set -u
cd "$HOME/epi_work" || exit 1
echo "== REMOVE COPY ARTIFACTS =="
rm -rf ./epi_formal/.git
rm -rf ./论文一_e_plus_pi/parallel_work/C/round2/__pycache__
rm -f ./论文一_e_plus_pi/第一阶段_e_plus_pi.aux ./论文一_e_plus_pi/第一阶段_e_plus_pi.log ./论文一_e_plus_pi/第一阶段_e_plus_pi.out
echo "== CRLF -> LF =="
for f in ./epi_formal/EpiFormal/FlintHills.lean ./epi_formal/EpiFormal/Measure.lean \
         ./epi_formal/EpiFormal/MeiburgConvergence.lean \
         ./论文一_e_plus_pi/parallel_work/A/round2/model_check.txt \
         ./论文一_e_plus_pi/parallel_work/D/axioms_output.txt \
         ./论文一_e_plus_pi/UnweightedCorrection.lean \
         ./论文一_e_plus_pi/第一阶段_e_plus_pi.tex \
         ./论文一_e_plus_pi/第二阶段修订/Phase2_revised.tex; do
  sed -i 's/\r$//' "$f"
done
echo "== ELAN DEFAULT =="
"$HOME/.elan/bin/elan" default leanprover/lean4:v4.35.0
"$HOME/.elan/bin/lean" --version
echo "== RECOUNT =="
find . -path './epi_formal/.lake' -prune -o -type f -print | wc -l
echo "== ADAPT DONE =="
