#!/bin/bash
# Anonymous verifier for pompetzki release v1.3.1 (Grok Bot accountability lane).
# Usage: verify-release-1.3.1.sh WORKDIR RECIPE_REPO_CHECKOUT [NAME=SHA256[:SIZE] ...]
# Writes WORKDIR/report.txt; exits nonzero on any mismatch. No auth, no tokens.
set -u
W=$1; REPO=$2; shift 2; mkdir -p "$W/assets"; cd "$W" || exit 2
API=https://api.github.com/repos/PompetzkiChris/pompetzki/releases/tags/v1.3.1
FAIL=0; R=report.txt; : > $R; say(){ echo "$*" | tee -a $R; }
curl -sSf "$API" -o release.json || { say "PENDING: release API not available"; exit 3; }
python3 - <<'PY' > asset-list.tsv
import json;r=json.load(open('release.json'))
for a in r['assets']: print(a['name'],a['size'],(a.get('digest') or 'none').replace('sha256:',''),a['browser_download_url'],sep='\t')
PY
python3 -c "import json;r=json.load(open('release.json'));print('tag',r['tag_name'],'target_commitish',r['target_commitish'],'assets',len(r['assets']),'draft',r['draft'])" | tee -a $R
TGT=$(git ls-remote --tags https://github.com/PompetzkiChris/pompetzki 'refs/tags/v1.3.1*' | awk '/\^\{\}$/{d=$1} !/\^\{\}$/{t=$1} END{print (d?d:t)}')
[ "$TGT" = c5253c0922f553b1ac8ef18240c1c372ff39657f ] && say "TAG MATCH v1.3.1 -> $TGT" || { say "TAG MISMATCH v1.3.1 -> $TGT"; FAIL=1; }
while IFS=$'\t' read n s d u; do [ -f "assets/$n" ] || curl -sSfL "$u" -o "assets/$n" || { say "DOWNLOAD FAIL $n"; FAIL=1; }; done < asset-list.tsv
SUMSALL=$(ls assets | grep -i 'sha256sums')
while IFS=$'\t' read n s d u; do
  ls_=$(stat -c%s "assets/$n"); h=$(sha256sum "assets/$n"|cut -c1-64)
  sm=$(for S in $SUMSALL; do tr -d "\r" < "assets/$S" | grep -E "[ *]$n\$"; done | cut -c1-64 | sort -u); echo "$SUMSALL" | grep -qx "$n" && sm=self
  st="size_api=$([ "$ls_" = "$s" ] && echo OK || echo BAD) digest_api=$([ "$h" = "$d" ] && echo OK || echo BAD) sums=$([ "$sm" = self ] && echo self || ([ "$sm" = "$h" ] && echo OK || echo ${sm:+BAD}${sm:-absent}))"
  case "$st" in *BAD*) FAIL=1;; esac
  say "ASSET $n size=$ls_ sha256=$h $st"
done < asset-list.tsv
for e in "$@"; do n=${e%%=*}; v=${e#*=}; eh=${v%%:*}; es=${v#*:}; [ "$es" = "$v" ] && es=
  f=$(ls assets | grep -F "$n" | head -1); [ -z "$f" ] && { say "CLAIM $n: asset not found"; FAIL=1; continue; }
  h=$(sha256sum "assets/$f"|cut -c1-64); sz=$(stat -c%s "assets/$f")
  ok=$([ "$h" = "$eh" ] && { [ -z "$es" ] || [ "$sz" = "$es" ]; } && echo MATCH || echo MISMATCH); [ $ok = MISMATCH ] && FAIL=1
  say "CLAIM $f expected=$eh${es:+/$es} actual=$h/$sz $ok"; done
# selected 22 packaging files vs recipe manifest
M=$REPO/repair/packaging/v9-judge-v6-1.3.1/PUBLIC-SOURCE-MANIFEST.json
for z in $(ls assets | grep -i '\.zip$'); do
  python3 - "assets/$z" "$M" <<'PY' | tee -a $R
import sys,json,zipfile,hashlib
z=zipfile.ZipFile(sys.argv[1]); m=json.load(open(sys.argv[2]))['files']; names=z.namelist(); n=0;bad=0;absent=0
for row in m:
    hits=[x for x in names if x.endswith('/'+row['package_relative_path']) or x==row['package_relative_path']]
    if not hits: absent+=1; continue
    for h in hits:
        n+=1; a=hashlib.sha256(z.read(h)).hexdigest(); bad+=a!=row['sha256']
        if a!=row['sha256']: print('  SEL-MISMATCH',h)
print(f"SELECTION {sys.argv[1].split('/')[-1]}: rows={len(m)} present={len(m)-absent} copies_checked={n} mismatches={bad}")
PY
done
grep -q 'SEL-MISMATCH\|mismatches=[1-9]' $R && FAIL=1
say "RESULT $([ $FAIL = 0 ] && echo PASS || echo FAIL)"; exit $FAIL
