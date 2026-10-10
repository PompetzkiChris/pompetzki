#!/bin/sh
# run-elf.sh IMAGE OUTFILE -- run the native image on every corpus file under WSL; one row per file:
#   path | verdict line | exit | wall ns
# Corpus: judge/replay-all.jdg, judge/replay-B0.jdg, judge/t5.jdg, judge/mut/*.jdg, sigma1/out/*.jdg, sigma1/out/mut/*.jdg
IMG="$1"; OUT="$2"
cd /mnt/c/ClaudeOutput/pompetzki || exit 2
: > "$OUT.tmp"
for f in judge/replay-all.jdg judge/replay-B0.jdg judge/t5.jdg judge/mut/*.jdg sigma1/out/*.jdg sigma1/out/mut/*.jdg; do
  s=$(date +%s%N)
  v=$("$IMG" < "$f")
  e=$?
  t=$(( $(date +%s%N) - s ))
  echo "$f | $v | $e | $t" >> "$OUT.tmp"
done
mv "$OUT.tmp" "$OUT"
