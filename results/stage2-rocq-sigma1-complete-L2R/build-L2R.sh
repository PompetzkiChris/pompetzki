#!/bin/sh
# build-L2R.sh - lane L2R: compile the lane's Rocq files in dependency order against the Cohen library
# (forcing-src/general, read only), print the assumptions of the main theorems, run coqchk on L2R.L2RSigma1 (which
# depends on every other lane file). Times from date. Run from this directory. L2RCases.v is written by agree.rkt
# (racket agree.rkt L2RCases.v, from sigma1/out); it is not rewritten here.
R=/c/ClaudeOutput/formalization-toolchain-20260924/tools/Rocq-Platform-2026.07.0-9.1/bin
C=/c/ClaudeOutput/pompetzki/forcing-src/general
L=/c/ClaudeOutput/pompetzki/lanes/L2R
echo "start $(date)"
for f in L2RLogic L2RArith L2RFin L2RSent L2RCases L2RAgree L2RSigma1 L2RAgreeMut; do
  s=$(date +%s)
  "$R/coqc.exe" -R "$C" Cohen -R "$L" L2R "$L/$f.v" || { echo "FAILED $f"; exit 1; }
  echo "compiled $f.v in $(( $(date +%s) - s )) s"
done
"$R/coqc.exe" -R "$C" Cohen -R "$L" L2R "$L/PrintAxAll.v"
s=$(date +%s)
"$R/coqchk.exe" -silent -o -R "$C" Cohen -R "$L" L2R L2R.L2RSigma1 || { echo "COQCHK FAILED"; exit 1; }
echo "coqchk L2R.L2RSigma1 in $(( $(date +%s) - s )) s"
echo "end $(date)"
