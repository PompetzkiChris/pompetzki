; reggate.pmp
; Embedded canonical-registry gate. Decimal integers, not spellings.
;
; AUTHREF is the same text literal as judge-v4.pmp at commit
; 63f45bbcaa88e370827d2dd2e95a6d422fb8c589. Whitespace is a delimiter.
; A numeric token is one to twelve digits and means its integer value,
; so 02 is 2 and 00 is 0. This program does not read REG0.canon, REG0_CANON,
; or any reference file. A refusal is printed here, before any proof check.
;
; It does not compute Gallina check_thm or check_batch. That correspondence
; is a separate obligation. Theorem REG0_ok in Cohen.RpInitOk is an established
; proof, not an axiom added here.
;
;   pompetzki reggate.pmp FILE.jdg
; Exit 0:
;   GATE
;   <n0>
;   706
; Exit 1: REJECT registry, then the interpreter check-zero line.

trace off
text AUTHREF "@@AUTHREF@@"
set rpos const AUTHREF
set rlim add AUTHREF AUTHREF_len

text JPATH arg
read J0 JPATH
set ipos const J0
set ilim add J0 J0_len
set ncanon const 706
set who const 0
set ph const 0

set pos const ipos
set lim const ilim
gosub SKIPWS
set t sub lim pos
set t sub t 4
when negative t goto BADPARSE
set c peek pos 1
set t sub c 74
when nonzero t goto BADPARSE
set q add pos 1
set c peek q 1
set t sub c 68
when nonzero t goto BADPARSE
set q add pos 2
set c peek q 1
set t sub c 71
when nonzero t goto BADPARSE
set q add pos 3
set c peek q 1
set t sub c 49
when nonzero t goto BADPARSE
set pos add pos 4
gosub ENDTOK
set ipos const pos

set who const 0
set pos const ipos
set lim const ilim
gosub RDTAG
set ipos const pos
set t sub tg 82
when nonzero t goto BADPARSE

set who const 0
set pos const ipos
set lim const ilim
gosub RDNUM
set ipos const pos
set n0 const num
set t sub n0 707
when negative t goto COUNTOK
goto BADCOUNT
label COUNTOK

set ei const 0
label ENT
set t sub ei n0
when negative t goto ENT1
goto AFTER
label ENT1
gosub CMPENTRY
set ei add ei 1
goto ENT

label AFTER
set who const 0
set pos const ipos
set lim const ilim
gosub RDTAG
set t sub tg 84
when nonzero t goto BADPARSE
goto GATEOK

label CMPENTRY
set ph const 0
set need const 1
label FLOOP
when zero need goto HYPS
gosub CMPTAG
set t sub tgv 101
when zero t goto FEQ
set t sub tgv 113
when zero t goto FEQ
set t sub tgv 112
when zero t goto FPRED
set t sub tgv 110
when zero t goto FLOOP
set t sub tgv 97
when zero t goto FLOOP
set t sub tgv 120
when zero t goto FLOOP
set t sub tgv 105
when zero t goto FBIN
set t sub tgv 107
when zero t goto FBIN
set t sub tgv 100
when zero t goto FBIN
set t sub tgv 98
when zero t goto FBIN
goto BADFORM
label FEQ
gosub CMPNUM
gosub CMPNUM
set need sub need 1
goto FLOOP
label FPRED
gosub CMPNUM
gosub CMPNUM
set arity const num
set t sub arity 1000001
when negative t goto FPRED1
goto BADPARSE
label FPRED1
set ai const 0
label FPARGS
set t sub ai arity
when negative t goto FPARG1
set need sub need 1
goto FLOOP
label FPARG1
gosub CMPNUM
set ai add ai 1
goto FPARGS
label FBIN
set need add need 1
goto FLOOP
label HYPS
set ph const 1
gosub CMPNUM
set hn const num
set t sub hn 100001
when negative t goto HCAP
goto BADPARSE
label HCAP
set hi const 0
label HLOOP
set t sub hi hn
when negative t goto HONE
goto HEND
label HONE
gosub CMPNUM
set hi add hi 1
goto HLOOP
label HEND
gosub EXPECTBANG
return

label CMPTAG
set who const 1
set pos const rpos
set lim const rlim
gosub RDTAG
set rpos const pos
set tgv const tg
set who const 0
set pos const ipos
set lim const ilim
gosub RDTAG
set ipos const pos
set t sub tg tgv
when nonzero t goto BADFORM
return

label CMPNUM
set who const 1
set pos const rpos
set lim const rlim
gosub RDNUM
set rpos const pos
set want const num
set who const 0
set pos const ipos
set lim const ilim
gosub RDNUM
set ipos const pos
set t sub num want
when nonzero t goto CMPNUMBAD
return
label CMPNUMBAD
when zero ph goto BADFORM
goto BADHYP

label EXPECTBANG
set who const 1
set pos const rpos
set lim const rlim
gosub SKIPWS
set t sub pos lim
when negative t goto EB1
goto BADEMBED
label EB1
set c peek pos 1
set t sub c 33
when nonzero t goto BADEMBED
set pos add pos 1
gosub ENDTOK
set rpos const pos
return

label SKIPWS
set t sub pos lim
when negative t goto SW2
return
label SW2
set c peek pos 1
set t sub c 32
when zero t goto SW3
set t sub c 10
when zero t goto SW3
set t sub c 13
when zero t goto SW3
set t sub c 9
when zero t goto SW3
return
label SW3
set pos add pos 1
goto SKIPWS

label ENDTOK
set t sub pos lim
when negative t goto ET1
return
label ET1
set c peek pos 1
set t sub c 32
when zero t goto ET2
set t sub c 10
when zero t goto ET2
set t sub c 13
when zero t goto ET2
set t sub c 9
when zero t goto ET2
goto BADWHO
label ET2
return

label RDNUM
gosub SKIPWS
set num const 0
set nd const 0
label RN1
set t sub pos lim
when negative t goto RN2
goto RN9
label RN2
set c peek pos 1
set d sub c 48
when negative d goto RN9
set t sub d 10
when negative t goto RN3
goto RN9
label RN3
set t sub nd 12
when negative t goto RN4
goto BADWHO
label RN4
set num mul num 10
set num add num d
set nd add nd 1
set pos add pos 1
goto RN1
label RN9
when zero nd goto BADWHO
gosub ENDTOK
return

label RDTAG
gosub SKIPWS
set t sub pos lim
when negative t goto RT1
goto BADWHO
label RT1
set tg peek pos 1
set pos add pos 1
gosub ENDTOK
return

label GATEOK
say "GATE"
show n0
show ncanon
goto END
label BADCOUNT
say "REJECT registry"
say "count"
show n0
show ncanon
goto DIE
label BADFORM
say "REJECT registry"
show ei
say "formula"
goto DIE
label BADHYP
say "REJECT registry"
show ei
say "hypotheses"
goto DIE
label BADPARSE
say "REJECT registry"
say "parse"
goto DIE
label BADEMBED
say "REJECT registry"
say "embed"
goto DIE
label BADWHO
when zero who goto BADPARSE
goto BADEMBED
label DIE
set bad const 1
check zero bad
label END
set done const 0
