#lang racket/base
(require racket/file racket/list racket/string racket/format racket/port)

(define output-directory "C:/ClaudeOutput/abschluss-repair-20261011/judge")
(define published-root "C:/ClaudeOutput/public-math-test-20261011-2115/source-review/public-main")
(define replay (build-path published-root "certificates/theorem29/replay-all.jdg"))
(define raw-entries
  (call-with-input-file replay
    (lambda (in)
      (unless (equal? (string-trim (read-line in)) "JDG1") (error 'reference "JDG1 header differs"))
      (unless (equal? (string-split (read-line in)) '("R" "706")) (error 'reference "registry count differs"))
      (for/list ([i (in-range 706)]) (string-trim (read-line in))))))

(define (parse-entry text)
  (define tokens (string-split text))
  (define rest tokens)
  (define (pop!) (when (null? rest) (error 'reference "entry ends early"))
    (begin0 (car rest) (set! rest (cdr rest))))
  (define (number!)
    (define value (pop!))
    (unless (regexp-match? #px"^[0-9]+$" value) (error 'reference "invalid integer"))
    (string->number value 10))
  (define (list!) (for/list ([i (in-range (number!))]) (number!)))
  (define (form!)
    (define tag (string->symbol (pop!)))
    (case tag
      [(e q) (vector tag (number!) (number!))]
      [(p) (vector tag (number!) (list!))]
      [(n a x) (vector tag (form!))]
      [(i k d b) (vector tag (form!) (form!))]
      [else (error 'reference "invalid form tag")]))
  (define form (form!))
  (define hypotheses (list!))
  (unless (null? rest) (error 'reference "extra registry-entry tokens"))
  (cons form hypotheses))
(define entries (map parse-entry raw-entries))
(define token-entries
  (for/list ([line (in-list raw-entries)])
    (for/list ([token (in-list (string-split line))])
      (if (regexp-match? #px"^[0-9]+$" token) (string->number token 10) token))))

(define (write-text path value)
  (call-with-output-file (build-path output-directory path) #:exists 'error
    (lambda (out) (display value out))))
(define (datum-text datum) (with-output-to-string (lambda () (write datum))))

(define module-source
  (string-append
   "#lang racket/base\n(require racket/list)\n"
   ";; Canonical registry data generated from the released replay.\n"
   ";; The Rocq CanonicalRegistryData theorem binds this data to proved REG0.\n"
   "(provide canonical-registry canonical-registry-length canonical-registry-entry\n"
   "         canonical-token-entries authenticated-prefix? authenticated-token-prefix?)\n"
   "(define canonical-registry '" (datum-text entries) ")\n"
   "(define canonical-token-entries '" (datum-text token-entries) ")\n"
   "(define canonical-registry-length 706)\n"
   "(define (canonical-registry-entry i) (list-ref canonical-registry i))\n"
   "(define (authenticated-prefix? candidate)\n"
   "  (and (list? candidate) (<= (length candidate) canonical-registry-length)\n"
   "       (for/and ([actual (in-list candidate)] [expected (in-list canonical-registry)])\n"
   "         (equal? actual expected))))\n"
   "(define (normalize-token token)\n"
   "  (cond [(exact-nonnegative-integer? token) token]\n"
   "        [(and (string? token) (regexp-match? #px\"^[0-9]+$\" token)) (string->number token 10)]\n"
   "        [(string? token) token]\n"
   "        [(symbol? token) (symbol->string token)]\n"
   "        [else #f]))\n"
   "(define (authenticated-token-prefix? candidate)\n"
   "  (and (list? candidate) (<= (length candidate) canonical-registry-length)\n"
   "       (for/and ([actual (in-list candidate)] [expected (in-list canonical-token-entries)])\n"
   "         (and (list? actual) (equal? (map normalize-token actual) expected)))))\n"))
(write-text "registry-auth-v4.rkt" module-source)

(define old-racket (file->string (build-path published-root "judge/racket/judge.rkt")))
(define auth-handler
  "(with-handlers ([(lambda (e) (and (pair? e) (eq? (car e) 'registry)))\n                   (lambda (e) (printf \"REJECT initial registry ~a: ~a\\n\" (cadr e) (caddr e)) 1)]\n                  [(lambda (e) (and (pair? e) (eq? (car e) 'parse)))")
(define racket-source
  (string-replace
   (string-replace
    (string-replace old-racket "#lang racket/base"
                    "#lang racket/base\n(require \"registry-auth-v4.rkt\")\n;; judge-v4 authenticates every initial registry entry before checking theorems.")
    "(with-handlers ([(lambda (e) (and (pair? e) (eq? (car e) 'parse)))" auth-handler)
   "(define entries (for/list ([_ (in-range n0)]) (let* ([d (form!)] [h (list!)]) (cons d h))))"
   "(when (> n0 canonical-registry-length) (raise (list 'registry 'count \"more than 706 entries\")))\n    (define entries (for/list ([i (in-range n0)])\n      (define entry (let* ([d (form!)] [h (list!)]) (cons d h)))\n      (unless (equal? entry (canonical-registry-entry i))\n        (raise (list 'registry i \"entry differs from canonical REG0\")))\n      entry))"))
(write-text "judge-v4.rkt" racket-source)

(define gate-code #<<PMP
; Authentication compares tags and exact decimal integers in the parsed entry span.
; AUTHREF contains every proved REG0 entry followed by the delimiter !.
label AUTHREG
set authsavedpos const pos
set authsavedlim const lim
set authipos const authentrypos
set authilim const pos
label AUTHNEXT
set pos const authrefpos
set lim const authreflim
gosub SKIPWS
set c peek pos 1
set t sub c 33
when zero t goto AUTHENDENTRY
set d sub c 48
when negative d goto AUTHTAG
set t sub d 10
when negative t goto AUTHNUM
goto AUTHTAG
label AUTHTAG
gosub RDTAG
set authwant const tg
set authrefpos const pos
set pos const authipos
set lim const authilim
gosub RDTAG
set authipos const pos
set t sub tg authwant
when nonzero t goto AUTHREGFAIL
goto AUTHNEXT
label AUTHNUM
gosub RDNUM
set authwant const num
set authrefpos const pos
set pos const authipos
set lim const authilim
gosub RDNUM
set authipos const pos
set t sub num authwant
when nonzero t goto AUTHREGFAIL
goto AUTHNEXT
label AUTHENDENTRY
gosub RDTAG
set authrefpos const pos
set pos const authipos
set lim const authilim
gosub SKIPWS
set t sub pos lim
when nonzero t goto AUTHREGFAIL
set pos const authsavedpos
set lim const authsavedlim
return
label AUTHREGFAIL
text WHY "initial registry entry differs from canonical REG0"
say "initial registry entry (counted from 0):"
show ri
goto FAIL
label AUTHCOUNTFAIL
text WHY "initial registry has more than 706 entries"
goto FAIL

PMP
)
(define reference-text (string-join (map (lambda (entry) (string-append entry " !")) raw-entries) " "))
(define old-pmp (file->string (build-path published-root "judge/judge-v3.pmp")))
(define pmp-source
  (string-replace
   (string-replace
    (string-replace
     (string-replace old-pmp "trace off\n"
       (string-append
        "; judge-v4.pmp authenticates initial registries against embedded proved REG0.\n"
        "; Original judge-v3 computation follows authentication; source-v3 is preserved.\n"
        "trace off\ntext AUTHREF \"" reference-text "\"\n"
        "set authrefpos const AUTHREF\nset authreflim add AUTHREF AUTHREF_len\n"))
     "set nreg const num\n" "set nreg const num\nset t sub nreg 707\nwhen negative t goto AUTHCOUNTOK\ngoto AUTHCOUNTFAIL\nlabel AUTHCOUNTOK\n")
    "label REGONE\ngosub PARSEF" "label REGONE\nset authentrypos const pos\ngosub PARSEF")
   "set rgf const pf\ngosub RDLIST\n" "set rgf const pf\ngosub RDLIST\ngosub AUTHREG\n"))
(write-text "judge-v4.pmp" (string-append (string-replace pmp-source "; ================================================================ reading\n" (string-append gate-code "; ================================================================ reading\n")) "\n"))

(define (coq-form f)
  (define tag (vector-ref f 0))
  (define (field i) (vector-ref f i))
  (case tag
    [(e) (format "(dE ~a ~a)" (field 1) (field 2))]
    [(q) (format "(dEq ~a ~a)" (field 1) (field 2))]
    [(p) (format "(dP ~a [~a])" (field 1) (string-join (map number->string (field 2)) ";"))]
    [(n a x) (format "(~a ~a)" (case tag [(n) "dN"] [(a) "dA"] [(x) "dX"]) (coq-form (field 1)))]
    [(i k d b) (format "(~a ~a ~a)" (case tag [(i) "dI"] [(k) "dK"] [(d) "dD"] [(b) "dQ"])
                        (coq-form (field 1)) (coq-form (field 2)))]))
(define coq-source
  (string-append
   "From Stdlib Require Import List NArith.\nFrom Cohen Require Import Replay2 RpInit.\nImport ListNotations.\nLocal Open Scope N_scope.\n"
   "Definition canonical_data : list entry := [\n"
   (string-join
    (for/list ([entry (in-list entries)])
      (format "(~a, [~a])" (coq-form (car entry)) (string-join (map number->string (cdr entry)) ";"))) ";\n")
   "].\n"))
(make-directory* (build-path output-directory "rocq"))
(write-text "rocq/CanonicalRegistryData.v" coq-source)
(write-text "REG0-canonical.jdg" (string-append "JDG1\nR 706\n" (string-join raw-entries "\n") "\nT 0\n"))
(write-text "REFERENCE-PROVENANCE.txt"
  (string-append "Released replay-all.jdg SHA256 a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae\n"
                 "Published source commit e8958a92d72c0b4cace72949510807b8a5b1320e\n"
                 "CanonicalRegistryData.canonical_data is the exact parsed data embedded by both repaired judges.\n"))
(printf "Generated ~a entries; embedded reference ~a characters.\n" (length entries) (string-length reference-text))
