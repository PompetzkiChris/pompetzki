#!/bin/sh
# v6 registry gate, then authenticated judge-v5.
# judge-v3 is not invoked. A registry refusal does not start the proof judge.
#
#   POMPETZKI   interpreter (default: pompetzki)
#   JUDGE_V5    judge-v5.pmp (default: judge/judge-v5.pmp from the repo root)
#
# Usage: judge-gated-v5.sh FILE.jdg
set -eu
DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$DIR/../../.." && pwd)
if [ "$#" -ne 1 ]; then
  echo "usage: judge-gated-v5.sh FILE.jdg" >&2
  exit 2
fi
FILE=$1
case $FILE in
  /*) ;;
  *)
    FILE=$(CDPATH= cd -- "$(dirname "$FILE")" && pwd)/$(basename "$FILE")
    ;;
esac
POMP=${POMPETZKI:-pompetzki}
JUDGE=${JUDGE_V5:-$ROOT/judge/judge-v5.pmp}
set +e
out=$("$POMP" "$DIR/reggate.pmp" "$FILE" 2>&1)
st=$?
set -e
printf '%s\n' "$out"
if [ "$st" -ne 0 ]; then
  exit "$st"
fi
first=$(printf '%s\n' "$out" | head -n 1)
if [ "$first" != "GATE" ]; then
  echo "reggate exited 0 without GATE" >&2
  exit 2
fi
"$POMP" "$JUDGE" "$FILE"
exit $?
