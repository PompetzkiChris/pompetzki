#!/usr/bin/env bash
# Rebuild branch binaries from this checkout and rerun the driver against v1.2.0 and the branch.
# Needs: nasm (2.16.03 used), GNU ld, racket (8.14 CS used), python3, curl, unzip.
set -u; H=$(cd "$(dirname "$0")" && pwd); R=$(cd "$H/../../.." && pwd); W=${WORK:-/tmp/pompetzki-acct}; mkdir -p "$W"; cd "$W"
B=https://github.com/PompetzkiChris/pompetzki/releases/download
for f in Abschluss-1.2-windows-x64.zip SHA256SUMS.txt; do curl -sL -o "v120-$f" "$B/v1.2.0/$f"; done
(sed 's/\*/*v120-/' v120-SHA256SUMS.txt | grep windows | sha256sum -c) || exit 9
for f in pompetzki-linux-x64-20261010.zip SHA256SUMS.txt; do curl -sL -o "rel-$f" "$B/v2026.10.10/$f"; done
(sed 's/\*/*rel-/' rel-SHA256SUMS.txt | grep linux | sha256sum -c) || exit 9
rm -rf w l; unzip -qo v120-Abschluss-1.2-windows-x64.zip -d w; unzip -qo rel-pompetzki-linux-x64-20261010.zip -d l; chmod +x l/bin/linux/*
nasm -DLINUX -f elf64 "$R/repair/runtime/source/pompetzki.asm" -o p.o && ld -o pompetzki-repaired-linux p.o || exit 9
rm -rf bl; python3 "$R/judge/native/portable/build-native.py" --source "$R/judge/judge-v4.pmp" --output bl --target linux >/dev/null || exit 9
sha256sum l/bin/linux/pompetzki pompetzki-repaired-linux bl/judge-v4-linux w/Abschluss-1.2/judge/judge-v3.pmp
rc=0
python3 "$H/driver.py" --label v120 --interp l/bin/linux/pompetzki --judge w/Abschluss-1.2/judge/judge-v3.pmp --strx w/Abschluss-1.2/tools/strx/strx.pmp; echo "v120 driver exit=$? (expected 1: defects present)"
python3 "$H/driver.py" --label branch --interp pompetzki-repaired-linux --judge bl/judge-v4-linux --strx "$R/repair/libraries/strx/strx.pmp" || rc=1
python3 "$H/driver.py" --label branch-v4pmp --interp pompetzki-repaired-linux --judge "$R/judge/judge-v4.pmp" --strx "$R/repair/libraries/strx/strx.pmp" || rc=1
echo "branch overall exit=$rc"; exit $rc
