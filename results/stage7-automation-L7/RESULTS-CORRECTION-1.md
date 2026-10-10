# Correction 1 to RESULTS.md (written 18:46, `date`)

RESULTS.md, section 1, "Instances": "40 random instances" is wrong. L7-1-equality.jdg holds **39** random congruence
instances. The driver draws 40 and keeps those that have a goal: a congruent pair not among the hypothesis equations, or
an atom that can be rewritten; one draw had neither. Count from out\L7-1-equality.index.txt: 39 keys "random …",
67 congruence theorems in all (28 from the families + 39 random), 9 chain theorems.

Also not in RESULTS.md's file list: src\assemble-v2.rkt (writes RESULTS.md and STATUS.txt from the drafts and the judge
tables; v1, which reached cmd's date command, is in src\superseded\).
