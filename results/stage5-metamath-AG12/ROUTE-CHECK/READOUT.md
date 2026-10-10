# Routed logic axiom instances

Created: 2026-10-09T19:13:11.6506186-04:00 (Get-Date).

10 of 10 files have ACCEPT and exit 0 from both judges. Each file has an empty numbered registry, one theorem, no declared hypotheses, and 1 or 3 steps. The files contain 12 steps in total.

The sample is ax-1 through ax-10. Membership and equality atoms provide free-variable instances. ax-4 uses quantifier bodies that depend on x. ax-5 retains the source disjoint condition by choosing a body independent of x. ax-10 starts with a body that depends on x; the body under its outer RHS binder is independent of that binder because its inner x binder shadows it. ax-6 derives the existential formula from reflexivity by E and M. ax-7 through ax-9 use substitution templates with the free z index retained.

None of these ten source axioms has essential hypotheses. This sample therefore does not test ax-mp or ax-gen with essential premises, nor does it validate every route in LOGIC-ROUTES.tsv. Each run receipt records the exact PowerShell command, judge working directory, Get-Date start and finish, exit code, verdict, and paths to separate stdout and stderr files. MANIFEST.tsv records the route and verdicts per label.

Source definitions: C:\ClaudeOutput\pompetzki\forcing-src\general\Replay2.v (axshape and sstep); serialization: C:\ClaudeOutput\pompetzki\judge\rocq2jdg.rkt.
