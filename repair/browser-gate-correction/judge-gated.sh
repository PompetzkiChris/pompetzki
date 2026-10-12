#!/bin/sh
# Credited correction of Grok's wrapper; default proof source is judge-v5.
set -eu
DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
if [ "$#" -ne 1 ]; then
  echo "usage: judge-gated.sh FILE.jdg" >&2
  exit 2
fi
FILE=$1
case $FILE in
  /*) ;;
  *) FILE=$(CDPATH= cd -- "$(dirname "$FILE")" && pwd)/$(basename "$FILE") ;;
esac
POMP=${POMPETZKI:-pompetzki}
JUDGE=${JUDGE_V5:-"$DIR/../../judge/judge-v5.pmp"}
if [ ! -f "$JUDGE" ]; then
  echo "judge-v5 source was not found; set JUDGE_V5 to its pathname" >&2
  exit 2
fi
set +e
out=$("$POMP" "$DIR/reggate.pmp" "$FILE" 2>&1)
st=$?
set -e
printf '%s\n' "$out"
if [ "$st" -ne 0 ]; then exit "$st"; fi
first=$(printf '%s\n' "$out" | head -n 1)
if [ "$first" != "GATE" ]; then
  echo "gate exited 0 without GATE" >&2
  exit 2
fi
if [ -n "${GATE_PROOF_LOG:-}" ]; then printf '%s\n' "$FILE" >> "$GATE_PROOF_LOG"; fi
"$POMP" "$JUDGE" "$FILE"
exit $?
