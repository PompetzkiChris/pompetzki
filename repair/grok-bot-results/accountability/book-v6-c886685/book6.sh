#!/bin/bash
# Independent Book v6 attack harness (Grok Bot accountability). Usage: book6.sh REPO BUNDLE OUTDIR
set -u
REPO=$1; B=$2; O=$3; BK=$REPO/repair/book-v6; W=/workspace/bw6; rm -rf $W; mkdir -p $W $O/raw $O/inputs
cp $REPO/judge/mut/ok-hyp.jdg $REPO/judge/mut/m1-refl.jdg $W/; cp $W/*.jdg $O/inputs/
run(){ n=$1; shift; (cd $BK && "$@") >$O/raw/$n.stdout 2>$O/raw/$n.stderr; echo $? >$O/raw/$n.exit; printf '%-34s exit=%s %s\n' "$n" "$(cat $O/raw/$n.exit)" "$(cat $O/raw/$n.stderr $O/raw/$n.stdout | tr '\n' ' ' | cut -c1-170)"; }
post(){ run "$1" racket verified-book-post.rkt "${@:3}" --bundle $B $W/$2 2026-10-11 ; }
chk(){ run "$1" racket verified-book-check.rkt --bundle $B $W/$2; }
run 01-post-default racket verified-book-post.rkt --bundle $B $W/post-default 2026-10-11 $W/ok-hyp.jdg
run 02-post-interpreted racket verified-book-post.rkt --interpreted --bundle $B $W/post-interp 2026-10-11 $W/ok-hyp.jdg
chk 03-check-default post-default
chk 04-check-interpreted post-interp
run 05-post-m1 racket verified-book-post.rkt --bundle $B $W/post-m1 2026-10-11 $W/m1-refl.jdg
chk 06-check-m1 post-m1
# v5 forgery dirs replayed unchanged against the v6 checker
for d in forge-consistent-false2 forge-rehashed forge-orphan-n forge-orphan-snapshot forge-changed-input forge-bad-f-sha forge-dup-receipt forge-reorder-B forge-wrong-bytes forge-bad-timestamp forge-orphan-file; do
  rm -rf $W/v5-$d; cp -a /workspace/bw5/$d $W/v5-$d; chk 10-v5replay-$d v5-$d; done
mk(){ rm -rf $W/$1; cp -a $W/post-default $W/$1; }
mk a-orphan-run; echo 'ACCEPT' > $W/a-orphan-run/judge-runs/orphan.stdout.txt; chk 20-orphan-judge-runs-file a-orphan-run
mk a-empty-runs; rm -f $W/a-empty-runs/judge-runs/*; chk 21-empty-judge-runs a-empty-runs
mk a-empty-inputs; rm -f $W/a-empty-inputs/judge-inputs/*; chk 22-empty-judge-inputs a-empty-inputs
mk a-extra-top; echo x > $W/a-extra-top/NOTES.txt; chk 23-extra-top-level-file a-extra-top
mk a-extra-topdir; mkdir $W/a-extra-topdir/extra; chk 24-extra-top-level-dir a-extra-topdir
mk a-nested; mkdir $W/a-nested/judge-runs/sub; chk 25-nested-dir-in-judge-runs a-nested
mk a-symlink; f=$(ls $W/a-symlink/judge-runs | head -1); mv $W/a-symlink/judge-runs/$f $W/$f.real; ln -s $W/$f.real $W/a-symlink/judge-runs/$f; chk 26-symlinked-run-file a-symlink
mk a-missing; f=$(ls $W/a-missing/judge-runs | head -1); rm $W/a-missing/judge-runs/$f; chk 27-missing-run-file a-missing
# duplicate output identity: two inputs with identical bytes posted together
cp $W/ok-hyp.jdg $W/ok-hyp-copy.jdg
run 28-post-duplicate-bytes racket verified-book-post.rkt --bundle $B $W/post-dup 2026-10-11 $W/ok-hyp.jdg $W/ok-hyp-copy.jdg
[ -d $W/post-dup ] && chk 29-check-duplicate-bytes post-dup
run 30-post-same-input-twice racket verified-book-post.rkt --bundle $B $W/post-same 2026-10-11 $W/ok-hyp.jdg $W/ok-hyp.jdg
[ -d $W/post-same ] && chk 31-check-same-input-twice post-same
ls -la $W/post-default $W/post-default/judge-runs $W/post-default/judge-inputs > $O/raw/posting-layout.txt
