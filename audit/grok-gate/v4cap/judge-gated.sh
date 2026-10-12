#!/bin/sh
# Registry gate, then the released pmp proof judge only after GATE.
# A registry refusal is not a proof verdict: judge-v3.pmp is not started.
# This script does not read REG0.canon. An external canon file is not authority.
#
#   POMPETZKI      interpreter (default: pompetzki)
#   JUDGE_V3       released judge-v3.pmp
#   GATE_PROOF_LOG if set, the proof-judge invocation appends the input path
#
# Usage: judge-gated.sh FILE.jdg
set -eu
DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
if [ "$#" -ne 1 ]; then
  echo "usage: judge-gated.sh FILE.jdg" >&2
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
if [ -n "${JUDGE_V3:-}" ]; then
  JUDGE=$JUDGE_V3
else
  echo "set JUDGE_V3 to the released judge-v3.pmp; this gate does not replace it" >&2
  exit 2
fi
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
if [ -n "${GATE_PROOF_LOG:-}" ]; then
  printf '%s\n' "$FILE" >> "$GATE_PROOF_LOG"
fi
"$POMP" "$JUDGE" "$FILE"
exit $?
