#lang racket/base
;; spotcheck.rkt -- book-master (Abschluss 1.0). Before a ledger is merged, 2 of its records are re-checked by
;; running BOTH judges again on the judged file the record names.
;;
;;   racket spotcheck.rkt plan inventory.tsv chainverify.tsv SHIPPED-BOOKDIR PLAN.tsv
;;   racket spotcheck.rkt run  PLAN.tsv OUTDIR
;;
;; plan: for every ledger that passed chainverify (and for the shipped Book), picks 2 records:
;;   BOOK ledger      2 B postings, from 2 different F files when the ledger has 2 or more;
;;   NEGATIVE ledger  2 N records (2 different files when it has 2 or more);
;;   shipped Book     2 B postings and 2 N records.
;;   A ledger with no B (or no N) has nothing to spot-check; its chain check stands alone (it merges no record).
;;   Candidates: files whose recorded pmp judge time is at most 300 s (so the re-run fits the 600 s limit; the limit
;;   is 540 s, then any, when no file qualifies), whose path exists and whose sha256 now equals the recorded one.
;;   Order of candidates: sha256("<pair>|<kind>|<k>") picks the file (index modulo the candidate count) and the theorem
;;   (modulo the file's theorem count); files already picked for an earlier ledger are taken only when no other
;;   candidate is left (copies of a ledger then check other files). Deterministic: the same inputs give the same plan.
;; run: runs each distinct picked file through both judges, at most 2 judge processes at once (2 lanes, each lane
;;   runs pmp then racket), each judge with a 600 s timeout, exactly as lanes\L9\tools\runjudges.rkt runs them:
;;     C:\ClaudeOutput\pompetzki\pompetzki.exe judge-v3.pmp FILE          (folder C:\ClaudeOutput\pompetzki\judge)
;;     "C:\Program Files\Racket\racket.exe" racket\judge.rkt FILE          (same folder)
;;   then decides each pick:
;;   B  PASS when the file sha256 equals the record's, both judges ACCEPT with exit 0, both judges' printed counts end
;;      in the F record's registry n0, theorems m, steps total, n0+m, and the B posting's fields recomputed from the
;;      file (book-post.rkt's JDG1 reader: entry, status, stmt, drv, steps, hyps, cites, ax, def, hypent, file,
;;      registry) equal the posting's. ("first" needs the whole ledger and is not recomputed here.)
;;   N  PASS when the sha256 matches and both judges REJECT with exit 1.
;;   Writes OUTDIR\VERDICTS.tsv (one V line per judge run, runjudges.rkt's format) and OUTDIR\SPOTCHECK.tsv (one row
;;   per pick, PASS or FAIL with the reason), and prints a summary per ledger. New files only.
(require racket/list racket/string racket/file racket/port racket/bytes)

(define JUDGE-DIR "C:\\ClaudeOutput\\pompetzki\\judge")
(define PMP-EXE "C:\\ClaudeOutput\\pompetzki\\pompetzki.exe")
(define RACKET-EXE "C:\\Program Files\\Racket\\racket.exe")
(define DATE-EXE "C:\\Program Files\\Git\\usr\\bin\\date.exe")
(define TIMEOUT-MS 600000)
(define REFERENCE "C:\\ClaudeOutput\\pompetzki\\judge\\replay-all.jdg")
(define AXN '#("Ext" "Pair" "Union" "Power" "Inf" "Found" "Choice"))

(define (hex bs) (apply string-append (for/list ([b bs]) (string-append (if (< b 16) "0" "") (number->string b 16)))))
(define (sha-hex bs) (hex (sha256-bytes bs)))
(define (sha256-file f) (call-with-input-file f (lambda (in) (hex (sha256-bytes in)))))
(define (canon bs) (string->bytes/utf-8 (string-join (string-split (bytes->string/latin-1 bs)) " ")))
(define (pad n w) (let ([s (number->string n)]) (string-append (make-string (max 0 (- w (string-length s))) #\0) s)))
(define (clean s) (regexp-replace* #rx"[\t\r\n]" s " "))

;; ------------------------------------------------------------------ JDG1 reader (book-post.rkt / bookcheck.rkt)
(struct rd (buf [pos #:mutable] lim))
(define (ws? b) (or (= b 32) (= b 9) (= b 10) (= b 13)))
(define (skip! r)
  (let loop () (when (and (< (rd-pos r) (rd-lim r)) (ws? (bytes-ref (rd-buf r) (rd-pos r))))
                 (set-rd-pos! r (add1 (rd-pos r))) (loop))))
(define (tok! r)
  (skip! r)
  (when (>= (rd-pos r) (rd-lim r)) (error 'jdg1 "unexpected end at ~a" (rd-pos r)))
  (define s (rd-pos r))
  (let loop () (when (and (< (rd-pos r) (rd-lim r)) (not (ws? (bytes-ref (rd-buf r) (rd-pos r)))))
                 (set-rd-pos! r (add1 (rd-pos r))) (loop)))
  (values s (rd-pos r)))
(define (num! r)
  (define-values (s e) (tok! r))
  (for/fold ([v 0]) ([i (in-range s e)])
    (define d (- (bytes-ref (rd-buf r) i) 48))
    (unless (<= 0 d 9) (error 'jdg1 "not a number at ~a" s))
    (+ (* v 10) d)))
(define (tag! r)
  (define-values (s e) (tok! r))
  (unless (= (- e s) 1) (error 'jdg1 "not a tag at ~a" s))
  (integer->char (bytes-ref (rd-buf r) s)))
(define (list! r) (define n (num! r)) (for/list ([_ (in-range n)]) (num! r)))
(define (form! r)
  (case (tag! r)
    [(#\e #\q) (num! r) (num! r)]
    [(#\p) (num! r) (list! r)]
    [(#\n #\a #\x) (form! r)]
    [(#\i #\k #\d #\b) (form! r) (form! r)]
    [else (error 'jdg1 "form tag at ~a" (rd-pos r))])
  (void))
(define (step! r on-use)
  (case (tag! r)
    [(#\U) (on-use (num! r)) (list! r)]
    [(#\S) (num! r) (list! r)]
    [(#\G #\M) (num! r) (num! r)]
    [(#\T) (list! r) (form! r)]
    [(#\E #\V) (num! r) (form! r)]
    [(#\L #\H) (num! r) (num! r) (form! r)]
    [(#\Z) (form! r) (form! r)]
    [(#\Y) (form! r)]
    [else (error 'jdg1 "step tag at ~a" (rd-pos r))])
  (void))
(define (read-registry r)
  (define-values (s e) (tok! r))
  (unless (equal? (subbytes (rd-buf r) s e) #"JDG1") (error 'jdg1 "no JDG1"))
  (unless (char=? (tag! r) #\R) (error 'jdg1 "no R"))
  (define n (num! r))
  (for/list ([_ (in-range n)])
    (skip! r)
    (define a (rd-pos r))
    (form! r) (list! r)
    (canon (subbytes (rd-buf r) a (rd-pos r)))))
(define (ranges bits lo hi)
  (define runs
    (let loop ([i lo] [run #f] [acc '()])
      (cond [(>= i hi) (reverse (if run (cons (cons run (sub1 i)) acc) acc))]
            [(bitwise-bit-set? bits i) (loop (add1 i) (or run i) acc)]
            [run (loop (add1 i) #f (cons (cons run (sub1 i)) acc))]
            [else (loop (add1 i) #f acc)])))
  (string-join (for/list ([p runs]) (if (= (car p) (cdr p)) (number->string (car p)) (format "~a-~a" (car p) (cdr p)))) ","))
(define (popcount-range bits lo hi) (for/sum ([i (in-range lo hi)]) (if (bitwise-bit-set? bits i) 1 0)))
(define (trace-fields bits n0)
  (define axs (for/list ([i (in-range (min 7 n0))] #:when (bitwise-bit-set? bits i)) (vector-ref AXN i)))
  (define dhi (min 677 n0))
  (define dc (if (> dhi 7) (popcount-range bits 7 dhi) 0))
  (define hc (if (> n0 677) (popcount-range bits 677 n0) 0))
  (list (if (null? axs) "ax -" (string-append "ax " (string-join axs " ")))
        (if (= dc 0) "def 0 -" (format "def ~a ~a" dc (ranges bits 7 dhi)))
        (if (= hc 0) "hypent -" (string-append "hypent " (ranges bits 677 n0)))))
(define ref-entries #f)
(define prior-results (make-hash))
(define (parse-file bs)
  (define r (rd bs 0 (bytes-length bs)))
  (define entries (read-registry r))
  (define n0 (length entries))
  (define prefix? (and (<= n0 (length ref-entries)) (equal? entries (take ref-entries n0))))
  (define reghex (sha-hex (bytes-join entries #" ")))
  (unless (char=? (tag! r) #\T) (error 'jdg1 "no T"))
  (define m (num! r))
  (define traces (make-vector m 0))
  (define thms
    (for/list ([j (in-range m)])
      (skip! r)
      (define a (rd-pos r))
      (form! r)
      (define se (rd-pos r))
      (list! r)
      (define ns (num! r))
      (define cites '())
      (define tr 0)
      (for ([_ (in-range ns)])
        (step! r (lambda (u)
                   (unless (memv u cites)
                     (set! cites (cons u cites))
                     (set! tr (bitwise-ior tr (if (< u n0) (arithmetic-shift 1 u) (vector-ref traces (- u n0)))))))))
      (define hyps (list! r))
      (define te (rd-pos r))
      (vector-set! traces j tr)
      (list j a se te ns (reverse cites) tr hyps)))
  (skip! r)
  (unless (= (rd-pos r) (rd-lim r)) (error 'jdg1 "text after the last theorem"))
  (values n0 reghex prefix? m (for/sum ([t thms]) (list-ref t 4)) thms))

;; ------------------------------------------------------------------ ledger reading
(define (split-tab s) (string-split s "\t" #:trim? #f))
(define (fld fs pfx) (for/first ([f fs] #:when (string-prefix? f pfx)) (substring f (string-length pfx))))
(define (ms-of verdict-text) ; "ACCEPT exit 0 S - E 1234 ms ..." -> 1234 or #f
  (define m (regexp-match #px" ([0-9]+) ms( |$)" verdict-text)) (and m (string->number (cadr m))))
(define (ints s) (map string->number (regexp-match* #px"\\d+" s)))

;; ledger-files: list of paths read in order (a BOOK/NEGATIVE ledger, or the shipped Book's segments)
(define (scan-records files want?)
  (for*/list ([f files]
              [ln (in-lines (open-input-file f) 'linefeed)]
              #:when (want? ln))
    (split-tab ln)))
(define (shipped-segments dir)
  (let loop ([k 1] [acc '()])
    (define p (build-path dir "book" (format "J~a.txt" (pad k 6))))
    (if (file-exists? p) (loop (add1 k) (cons (path->string p) acc)) (reverse acc))))

;; ------------------------------------------------------------------ plan
(define picked-shas (make-hash))
(define present-cache (make-hash))
;; Files posted on the R13 exist there only; code\fetch-r13.sh copies them to MIRROR\<path without the drive>.
(define MIRROR "C:\\ClaudeOutput\\pompetzki\\release-1.0\\book-master\\r13-fetch\\")
(define (mirror-of path) (let ([m (regexp-match #px"^[A-Za-z]:\\\\(.*)$" path)]) (and m (string-append MIRROR (cadr m)))))
;; -> the path to judge (the recorded one, else its R13 copy) when its sha256 is the recorded one, else #f
(define (present? path sha)
  (hash-ref! present-cache (cons path sha)
             (lambda ()
               (cond [(and (file-exists? path) (equal? (sha256-file path) sha)) path]
                     [(let ([mp (mirror-of path)]) (and mp (file-exists? mp) (equal? (sha256-file mp) sha) mp))]
                     [else #f]))))
(define (seed-int s) (for/fold ([v 0]) ([b (sha256-bytes (string->bytes/utf-8 s))]) (+ (* v 256) b)))

;; cands: list of (id path sha bytes ms theorems extra ...) ; returns up to 2 picks: (cand theorem-index)
(define (choose pair kind cands report)
  ;; tiers by the recorded pmp time: 60 s, else 300 s, else 540 s (a file without a recorded time counts in the last
  ;; tier); a file whose recorded pmp time is over 540 s cannot be re-judged inside the 600 s limit and is not picked
  (define (eligible lim) (filter (lambda (c) (let ([ms (list-ref c 4)]) (if ms (<= ms lim) (= lim 540000)))) cands))
  (define pool (let ([a (eligible 60000)]) (if (pair? a) a (let ([b (eligible 300000)]) (if (pair? b) b (eligible 540000))))))
  (report (length cands) (length pool))
  (let loop ([k 1] [picks '()] [used-files '()] [tries 0])
    (cond
      [(or (= (length picks) 2) (> tries 400) (null? pool)) (reverse picks)]
      [else
       (define s (seed-int (format "~a|~a|~a" pair kind (+ k tries))))
       (define fresh (filter (lambda (c) (and (not (member (list-ref c 2) used-files)) (not (hash-ref picked-shas (list-ref c 2) #f)))) pool))
       (define notused (filter (lambda (c) (not (member (list-ref c 2) used-files))) pool))
       (define from (cond [(pair? fresh) fresh] [(pair? notused) notused] [else pool]))
       (define c (list-ref from (modulo s (length from))))
       (define usable (present? (list-ref c 1) (list-ref c 2)))
       (cond
         [(not usable)
          ;; absent or changed: never picked again, recorded as such
          (set! pool (remove c pool))
          (printf "  ~a ~a: ~a not present with sha256 ~a, skipped\n" pair kind (list-ref c 1) (list-ref c 2))
          (if (null? pool) (reverse picks) (loop k picks used-files (add1 tries)))]
         [else
          (define m (max 1 (list-ref c 5)))
          (define j (modulo (quotient s 1000003) m))
          (hash-set! picked-shas (list-ref c 2) #t)
          (loop (add1 k) (cons (list c j usable) picks) (cons (list-ref c 2) used-files) tries)])])))

(define (plan inv cv shipped out)
  (when (file-exists? out) (eprintf "REFUSED: ~a exists\n" out) (exit 1))
  (define pass (make-hash))
  (for ([ln (cdr (file->lines cv))])
    (define c (split-tab ln))
    (when (equal? (list-ref c 5) "PASS") (hash-set! pass (list-ref c 3) #t)))
  (define rows (for/list ([ln (file->lines inv)] #:unless (regexp-match? #rx"^(#|order\t)" ln)) (split-tab ln)))
  (define o (open-output-file out #:exists 'error))
  (fprintf o "pair\tkind\tledger\tpick\trecord\tF\tfile\tsha256\tbytes\tregistry_n0\ttheorems\tsteps\tpmp_ms_recorded\tcandidates\tpool\tnote\n")
  (define (emit pair kind ledger picks cands-n pool-n rec-of)
    (for ([p picks] [k (in-naturals 1)])
      (define c (car p)) (define j (cadr p)) (define usable (caddr p))
      (define-values (rec fid n0 m steps) (rec-of c j))
      (fprintf o "~a\n" (string-join (list pair kind ledger (number->string k) rec fid usable (list-ref c 2)
                                           (number->string (list-ref c 3)) n0 m steps
                                           (let ([ms (list-ref c 4)]) (if ms (number->string ms) "-"))
                                           (number->string cands-n) (number->string pool-n)
                                           (if (equal? usable (list-ref c 1)) "-" (string-append "R13 copy of " (list-ref c 1)))) "\t")))
    (when (null? picks)
      (fprintf o "~a\n" (string-join (list pair kind ledger "0" "-" "-" "-" "-" "-" "-" "-" "-" "-" (number->string cands-n) (number->string pool-n)
                                           (cond [(= cands-n 0) (format "no ~a record" kind)]
                                                 [(= pool-n 0) "no file with a recorded pmp time of 540 s or less"]
                                                 [else "no candidate file present with its recorded sha256"])) "\t"))))
  ;; F candidates: (Fid path sha bytes ms theorems n0 steps bfirst)
  (define (f-cands recs)
    (for/list ([fs recs] #:when (regexp-match? #px"^F[0-9]{6}$" (car fs)))
      (define reg (regexp-match #px"^registry ([0-9]+) prefix" (list-ref fs 5)))
      (define post (regexp-match #px"^postings B([0-9]+)-B([0-9]+)$" (list-ref fs 11)))
      (list (car fs) (fld fs "file ") (fld fs "sha256 ") (string->number (fld fs "bytes "))
            (ms-of (substring (list-ref fs 8) 4)) (string->number (fld fs "theorems "))
            (cadr reg) (fld fs "steps ") (string->number (cadr post)))))
  (define (n-cands recs)
    (for/list ([fs recs] #:when (regexp-match? #px"^N[0-9]{6}$" (car fs)))
      (list (car fs) (fld fs "file ") (fld fs "sha256 ") (string->number (fld fs "bytes "))
            (ms-of (substring (list-ref fs 6) 4)) 1)))
  (define (b-rec c j) (values (format "B~a" (pad (+ (list-ref c 8) j) 7)) (car c) (list-ref c 6) (number->string (list-ref c 5)) (list-ref c 7)))
  (define (n-rec c j) (values (car c) "-" "-" "-" "-"))
  (define (do-book pair ledger-label files)
    (define recs (scan-records files (lambda (ln) (regexp-match? #rx"^F[0-9]" ln))))
    (define cs (f-cands recs))
    (define pn 0) (define cn 0)
    (define picks (if (null? cs) '() (choose pair "B" cs (lambda (a b) (set! cn a) (set! pn b)))))
    (emit pair "B" ledger-label picks (length cs) pn b-rec))
  (define (do-neg pair ledger-label files)
    (define recs (scan-records files (lambda (ln) (regexp-match? #rx"^N[0-9]" ln))))
    (define cs (n-cands recs))
    (define pn 0) (define cn 0)
    (define picks (if (null? cs) '() (choose pair "N" cs (lambda (a b) (set! cn a) (set! pn b)))))
    (emit pair "N" ledger-label picks (length cs) pn n-rec))
  ;; shipped Book first
  (define segs (shipped-segments shipped))
  (do-book "SHIPPED" (path->string (path->complete-path shipped)) segs)
  (do-neg "SHIPPED" (path->string (path->complete-path shipped)) segs)
  (for ([r rows])
    (define pair (list-ref r 1)) (define bk (list-ref r 2)) (define ng (list-ref r 6))
    (when (and (not (equal? bk "-")) (hash-ref pass bk #f)) (do-book pair bk (list bk)))
    (when (and (not (equal? ng "-")) (hash-ref pass ng #f)) (do-neg pair ng (list ng))))
  (close-output-port o)
  (printf "wrote ~a; distinct files picked ~a\n" out (hash-count picked-shas)))

;; ------------------------------------------------------------------ run
(define (run-capture exe args #:dir [dir #f] #:timeout [timeout #f])
  (parameterize ([current-directory (or dir (current-directory))])
    (define-values (sp out in err) (apply subprocess #f #f #f exe args))
    (close-output-port in)
    (define out-str #f) (define err-str #f)
    (define t1 (thread (lambda () (set! out-str (port->string out)))))
    (define t2 (thread (lambda () (set! err-str (port->string err)))))
    (define done (sync/timeout (and timeout (/ timeout 1000)) sp))
    (define timed-out (not done))
    (when timed-out (subprocess-kill sp #t))
    (subprocess-wait sp)
    (thread-wait t1) (thread-wait t2)
    (close-input-port out) (close-input-port err)
    (values (subprocess-status sp) (string-append out-str (if (string=? err-str "") "" (string-append " / stderr: " err-str))) timed-out)))
(define (now-date) (let-values ([(c s t) (run-capture DATE-EXE (list "+%Y-%m-%d %H:%M:%S %Z"))]) (string-trim s)))
(define (one-line s) (string-join (filter (lambda (x) (not (string=? x ""))) (map string-trim (regexp-split #rx"\r?\n" s))) " / "))
(define (verdict-of code out timed-out)
  (define first (let ([ls (filter (lambda (x) (not (string=? x ""))) (map string-trim (regexp-split #rx"\r?\n" out)))]) (if (null? ls) "" (car ls))))
  (cond [timed-out "TIMEOUT"]
        [(and (= code 0) (regexp-match? #rx"^ACCEPT" first)) "ACCEPT"]
        [(and (= code 1) (regexp-match? #rx"^REJECT" first)) "REJECT"]
        [(and (= code 1) (regexp-match? #rx"^LIMIT" first)) "LIMIT"]
        [else "ERROR"]))
(define (judge-once file sha bytes judge)
  (define start (now-date))
  (define t0 (current-milliseconds))
  (define-values (code out timed-out)
    (if (eq? judge 'pmp)
        (run-capture PMP-EXE (list "judge-v3.pmp" file) #:dir JUDGE-DIR #:timeout TIMEOUT-MS)
        (run-capture RACKET-EXE (list "racket\\judge.rkt" file) #:dir JUDGE-DIR #:timeout TIMEOUT-MS)))
  (define ms (- (current-milliseconds) t0))
  (define end (now-date))
  (list "V" file sha (number->string bytes) (symbol->string judge) (verdict-of code out timed-out)
        (number->string code) start end (number->string ms) (one-line out)))

(define (find-record ledger-or-dir id)
  (define files (if (directory-exists? ledger-or-dir) (shipped-segments ledger-or-dir) (list ledger-or-dir)))
  (define pfx (string-append id "\t"))
  (for*/first ([f files] [ln (in-lines (open-input-file f) 'linefeed)] #:when (string-prefix? ln pfx)) (split-tab ln)))

(define (counts-ok? out n0 m total)
  (define v (ints out))
  (and (>= (length v) 4) (equal? (take-right v 4) (list n0 m total (+ n0 m)))))

(define (check-b pk vp vr)
  ;; pk: plan row; vp/vr: V lines. returns (values ok? reason)
  (define ledger (list-ref pk 2)) (define rec (list-ref pk 4)) (define fid (list-ref pk 5))
  (define path (list-ref pk 6)) (define sha (list-ref pk 7))
  (define n0 (string->number (list-ref pk 9))) (define m (string->number (list-ref pk 10))) (define total (string->number (list-ref pk 11)))
  (define b (find-record ledger rec))
  (define f (find-record ledger fid))
  (define problems '())
  (define (bad! fmt . a) (set! problems (cons (apply format fmt a) problems)))
  (unless (and (equal? (list-ref vp 5) "ACCEPT") (equal? (list-ref vp 6) "0")) (bad! "pmp ~a exit ~a" (list-ref vp 5) (list-ref vp 6)))
  (unless (and (equal? (list-ref vr 5) "ACCEPT") (equal? (list-ref vr 6) "0")) (bad! "racket ~a exit ~a" (list-ref vr 5) (list-ref vr 6)))
  (unless (counts-ok? (list-ref vp 10) n0 m total) (bad! "pmp printed counts differ from F (~a ~a ~a)" n0 m total))
  (unless (counts-ok? (list-ref vr 10) n0 m total) (bad! "racket printed counts differ from F (~a ~a ~a)" n0 m total))
  (cond
    [(not b) (bad! "record ~a not found" rec)]
    [(not f) (bad! "record ~a not found" fid)]
    [else
     (define bs (file->bytes path))
     (unless (equal? (sha-hex bs) sha) (bad! "file sha256 changed"))
     (define-values (rn0 reghex prefix? rm rtotal thms) (parse-file bs))
     (define bfirst (string->number (cadr (regexp-match #px"^postings B([0-9]+)-" (list-ref f 11)))))
     (define j (string->number (fld b "thm ")))
     (define t (list-ref thms j))
     (define-values (_j a se te ns cites tr hyps) (apply values t))
     (define expect
       (append
        (list (format "thm ~a" j) (format "entry ~a" (+ rn0 j)) (if (null? hyps) "Proved" "Qualified")
              (string-append "stmt " (sha-hex (canon (subbytes bs a se))))
              (string-append "drv " (sha-hex (canon (subbytes bs a te))))
              (format "steps ~a" ns)
              (if (null? hyps) "hyps -" (string-append "hyps " (string-join (map number->string hyps) ",")))
              (if (null? cites) "cites -"
                  (string-append "cites " (string-join (for/list ([u cites]) (if (< u rn0) (format "R~a" u) (format "B~a" (pad (+ bfirst (- u rn0)) 7)))) " "))))
        (trace-fields tr rn0)
        (list (string-append "file " sha) (string-append "registry " reghex))))
     (define got (list (list-ref b 2) (list-ref b 3) (list-ref b 4) (list-ref b 5) (list-ref b 6) (list-ref b 7) (list-ref b 8)
                       (list-ref b 10) (list-ref b 11) (list-ref b 12) (list-ref b 13) (list-ref b 14) (list-ref b 15)))
     (for ([e expect] [g got]) (unless (equal? e g) (bad! "field ~s, recomputed ~s" g e)))
     (unless prefix? (bad! "registry not a prefix of REG0"))
     (unless (and (= rn0 n0) (= rm m) (= rtotal total)) (bad! "file counts ~a ~a ~a, F ~a ~a ~a" rn0 rm rtotal n0 m total))])
  (values (null? problems) (if (null? problems) "both ACCEPT exit 0; counts and 13 posting fields recomputed equal" (string-join (reverse problems) "; "))))

(define (check-n pk vp vr)
  (define problems '())
  (define (bad! fmt . a) (set! problems (cons (apply format fmt a) problems)))
  (unless (and (equal? (list-ref vp 5) "REJECT") (equal? (list-ref vp 6) "1")) (bad! "pmp ~a exit ~a" (list-ref vp 5) (list-ref vp 6)))
  (unless (and (equal? (list-ref vr 5) "REJECT") (equal? (list-ref vr 6) "1")) (bad! "racket ~a exit ~a" (list-ref vr 5) (list-ref vr 6)))
  (unless (equal? (list-ref vp 2) (list-ref pk 7)) (bad! "file sha256 changed"))
  (values (null? problems) (if (null? problems) "both REJECT exit 1" (string-join (reverse problems) "; "))))

;; prior: verdict files of earlier runs (their files are not judged again); ascending?: smallest recorded time first
(define (run planf outdir [prior '()] [ascending? #f])
  (define vout (build-path outdir "VERDICTS.tsv"))
  (define sout (build-path outdir "SPOTCHECK.tsv"))
  (when (or (file-exists? vout) (file-exists? sout)) (eprintf "REFUSED: output exists\n") (exit 1))
  (set! ref-entries (let* ([b (file->bytes REFERENCE)] [r (rd b 0 (bytes-length b))]) (read-registry r)))
  (set! prior-results (load-verdicts prior))
  (define picks (for/list ([ln (cdr (file->lines planf))]) (split-tab ln)))
  (define real (filter (lambda (p) (not (equal? (list-ref p 3) "0"))) picks))
  ;; distinct files, largest recorded pmp time first so the long runs overlap (or smallest first)
  (define files (make-hash))
  (for ([p real] #:unless (hash-ref prior-results (list-ref p 7) #f))
    (hash-set! files (list-ref p 7) (list (list-ref p 6) (list-ref p 7) (string->number (list-ref p 8))
                                          (or (string->number (list-ref p 12)) 0))))
  (define jobs (sort (hash-values files) (if ascending? < >) #:key cadddr))
  (define vo (open-output-file vout #:exists 'error))
  (fprintf vo "# spotcheck.rkt run, started ~a; pmp judge ~a judge-v3.pmp FILE (folder ~a) pompetzki.exe sha256 ~a judge-v3.pmp sha256 ~a; racket judge ~a racket\\judge.rkt FILE judge.rkt sha256 ~a; timeout ~a ms; 2 lanes\n"
           (now-date) PMP-EXE JUDGE-DIR (sha256-file PMP-EXE) (sha256-file (build-path JUDGE-DIR "judge-v3.pmp"))
           RACKET-EXE (sha256-file (build-path JUDGE-DIR "racket" "judge.rkt")) TIMEOUT-MS)
  (flush-output vo)
  (define results (make-hash))
  (define q (make-semaphore 1))
  (define queue jobs)
  (define done 0)
  (define (take!) (call-with-semaphore q (lambda () (if (null? queue) #f (let ([j (car queue)]) (set! queue (cdr queue)) j)))))
  (define lanes
    (for/list ([w 2])
      (thread
       (lambda ()
         (let loop ()
           (define j (take!))
           (when j
             (define vp (judge-once (car j) (cadr j) (caddr j) 'pmp))
             (define vr (judge-once (car j) (cadr j) (caddr j) 'racket))
             (call-with-semaphore q (lambda ()
                                      (hash-set! results (cadr j) (cons vp vr))
                                      (set! done (add1 done))
                                      (fprintf vo "~a\n~a\n" (string-join vp "\t") (string-join vr "\t")) (flush-output vo)
                                      (printf "[~a/~a] ~a pmp ~a ~a ms, racket ~a ~a ms\n" done (length jobs) (car j)
                                              (list-ref vp 5) (list-ref vp 9) (list-ref vr 5) (list-ref vr 9))
                                      (flush-output)))
             (loop)))))))
  (for-each thread-wait lanes)
  (fprintf vo "# ended ~a\n" (now-date))
  (close-output-port vo)
  (for ([(k v) prior-results]) (hash-ref! results k v))
  (evaluate picks results sout)
  (printf "judged files ~a this run\n" (length jobs))
  (printf "wrote ~a and ~a\n" vout sout))

;; V lines of verdict files -> sha -> (pmp-line . racket-line), for files with both lines
(define (load-verdicts files)
  (define p (make-hash)) (define r (make-hash))
  (for* ([f files] [ln (file->lines f)] #:when (regexp-match? #rx"^V\t" ln))
    (define v (split-tab ln))
    (hash-set! (if (equal? (list-ref v 4) "pmp") p r) (list-ref v 2) v))
  (for/hash ([(k v) p] #:when (hash-ref r k #f)) (values k (cons v (hash-ref r k)))))

;; one SPOTCHECK row per pick; a pick whose file has no verdicts yet is PENDING
(define (evaluate picks results sout)
  (when (not ref-entries) (set! ref-entries (let* ([b (file->bytes REFERENCE)] [r (rd b 0 (bytes-length b))]) (read-registry r))))
  (define so (open-output-file sout #:exists 'error))
  (fprintf so "pair\tkind\tledger\tpick\trecord\tfile\tsha256\tresult\tpmp\tracket\treason\n")
  (define per (make-hash))
  (for ([p picks])
    (define pair (list-ref p 0)) (define kind (list-ref p 1))
    (cond
      [(equal? (list-ref p 3) "0")
       (fprintf so "~a\n" (string-join (list pair kind (list-ref p 2) "0" "-" "-" "-" "NONE" "-" "-"
                                             (format "nothing re-judged: ~a (candidates ~a, eligible by time ~a)" (list-ref p 15) (list-ref p 13) (list-ref p 14))) "\t"))
       (hash-update! per (cons pair kind) (lambda (l) (cons 'none l)) '())]
      [(not (hash-ref results (list-ref p 7) #f))
       (fprintf so "~a\n" (string-join (list pair kind (list-ref p 2) (list-ref p 3) (list-ref p 4) (list-ref p 6) (list-ref p 7)
                                             "PENDING" "-" "-" "the judges have not run on this file yet") "\t"))
       (hash-update! per (cons pair kind) (lambda (l) (cons 'pending l)) '())]
      [else
       (define v (hash-ref results (list-ref p 7)))
       (define-values (ok why)
         (with-handlers ([exn:fail? (lambda (e) (values #f (clean (exn-message e))))])
           (if (equal? kind "B") (check-b p (car v) (cdr v)) (check-n p (car v) (cdr v)))))
       (fprintf so "~a\n" (string-join (list pair kind (list-ref p 2) (list-ref p 3) (list-ref p 4) (list-ref p 6) (list-ref p 7)
                                             (if ok "PASS" "FAIL")
                                             (format "~a exit ~a ~a ms" (list-ref (car v) 5) (list-ref (car v) 6) (list-ref (car v) 9))
                                             (format "~a exit ~a ~a ms" (list-ref (cdr v) 5) (list-ref (cdr v) 6) (list-ref (cdr v) 9))
                                             why) "\t"))
       (hash-update! per (cons pair kind) (lambda (l) (cons (if ok 'pass 'fail) l)) '())]))
  (close-output-port so)
  (define npass 0) (define nfail 0) (define npend 0)
  (for ([(k l) per]) (cond [(memq 'fail l) (set! nfail (add1 nfail))] [(memq 'pending l) (set! npend (add1 npend))] [else (set! npass (add1 npass))]))
  (printf "ledgers: spot-check PASS (or nothing to check) ~a, FAIL ~a, PENDING ~a\n" npass nfail npend))

(module+ main
  (define args (vector->list (current-command-line-arguments)))
  (cond
    [(and (= (length args) 5) (equal? (car args) "plan"))
     (plan (list-ref args 1) (list-ref args 2) (list-ref args 3) (list-ref args 4))]
    [(and (= (length args) 3) (equal? (car args) "run")) (run (list-ref args 1) (list-ref args 2))]
    ;; run-small PLAN OUTDIR PRIOR-VERDICTS ... : smallest recorded time first, files with prior verdicts not re-run
    [(and (>= (length args) 3) (equal? (car args) "run-small")) (run (list-ref args 1) (list-ref args 2) (list-tail args 3) #t)]
    ;; check PLAN OUT.tsv VERDICTS ... : evaluates the picks from verdict files now (PENDING where none yet)
    [(and (>= (length args) 4) (equal? (car args) "check"))
     (evaluate (for/list ([ln (cdr (file->lines (list-ref args 1)))]) (split-tab ln)) (load-verdicts (list-tail args 3)) (list-ref args 2))]
    [else (eprintf "usage: racket spotcheck.rkt plan inventory.tsv chainverify.tsv SHIPPED-BOOKDIR PLAN.tsv\n       racket spotcheck.rkt run PLAN.tsv OUTDIR\n") (exit 2)]))
