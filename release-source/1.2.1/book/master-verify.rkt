#lang racket/base
;; master-verify.rkt -- book-master (Abschluss 1.0). Checks a master Book against SPEC.md and against its sources.
;;   racket master-verify.rkt MASTERDIR
;; Reads only. MASTERDIR holds book\J000001.txt ... and DUPLICATES*.tsv. Checks:
;;  journal  chain over all segments (chain(0) = 64 zeros); H names the previous segment and its sha256; ids per kind
;;           1, 2, 3 ... without gaps; field counts H 10, F 20, B 24, N 12, S 12, E 10 (+ chain); E records/ranges/
;;           duplicates; every B: status agrees with hyps, "pmp ACCEPT", "racket ACCEPT", pmp-verdict/racket-verdict/
;;           verdicts/receipt equal its F's fields 8/9/10/16; no two B with the same (stmt, drv); first = the earliest
;;           B with the same stmt; cites name earlier B ids; F postings = its booked B ids; booked + duplicates =
;;           theorems; every N has both REJECT verdicts.
;;  sources  per segment, the source ledger(s) named in H: sha256 now = H's, chain recomputed = H head, records = H's;
;;           every source F/B/N/S is either booked here (its master record's "from" names its id and chain, and every
;;           copied field is byte-equal; B cites map to master ids) or a DUPLICATES row whose booked_as is a master
;;           record with the same key (B: stmt and drv; F/N/S: file sha256); the E duplicates counts equal those rows.
;; Prints the counts and MASTER CHECK OK (exit 0), or the first 60 differences and MASTER CHECK FAILED (exit 1).
(require racket/list racket/string racket/file)

(define L9-VERDICTS "C:\\ClaudeOutput\\pompetzki\\lanes\\L9\\verdicts\\")
(define AXN '("Ext" "Pair" "Union" "Power" "Inf" "Found" "Choice"))
(define ZERO (make-string 64 #\0))
(define (hex bs) (apply string-append (for/list ([b bs]) (string-append (if (< b 16) "0" "") (number->string b 16)))))
(define (sha256-file f) (call-with-input-file f (lambda (in) (hex (sha256-bytes in)))))
(define (L s) (string->bytes/latin-1 s))
(define (chain-of prev body) (hex (sha256-bytes (bytes-append (L prev) #"\n" (L body)))))
(define (split-tab s) (string-split s "\t" #:trim? #f))
(define (fld fs pfx) (for/first ([f fs] #:when (string-prefix? f pfx)) (substring f (string-length pfx))))
(define (pad n w) (let ([s (number->string n)]) (string-append (make-string (max 0 (- w (string-length s))) #\0) s)))
(define (id kind n) (string-append kind (pad n (if (equal? kind "B") 7 6))))
(define problems 0)
(define (diff! fmt . a) (set! problems (add1 problems)) (when (<= problems 60) (printf "DIFF ~a\n" (apply format fmt a))))
(define (lines-of path)
  (call-with-input-file path
    (lambda (in) (let loop ([acc '()]) (define b (read-bytes-line in 'linefeed))
                   (if (eof-object? b) (reverse acc) (loop (cons (bytes->string/latin-1 b) acc)))))))
(define (for-lines path proc)
  (call-with-input-file path
    (lambda (in) (let loop () (define b (read-bytes-line in 'linefeed))
                   (unless (eof-object? b) (proc (bytes->string/latin-1 b)) (loop))))))

;; trace union and ranges (same rules as book-post.rkt's trace-fields output)
(define (parse-ranges s)
  (if (equal? s "-") '()
      (append* (for/list ([p (string-split s ",")])
                 (define m (regexp-match #px"^([0-9]+)-([0-9]+)$" p))
                 (if m (for/list ([i (in-range (string->number (cadr m)) (add1 (string->number (caddr m))))]) i) (list (string->number p)))))))
(define (render-ranges ints)
  (define xs (sort (remove-duplicates ints) <))
  (let loop ([xs xs] [acc '()])
    (cond [(null? xs) (string-join (reverse acc) ",")]
          [else (define a (car xs))
                (let run ([b a] [r (cdr xs)])
                  (if (and (pair? r) (= (car r) (add1 b))) (run (car r) (cdr r))
                      (loop r (cons (if (= a b) (number->string a) (format "~a-~a" a b)) acc))))])))
(define (trace-union bs)
  (define axs (make-hash)) (define defs '()) (define hyps '())
  (for ([b bs])
    (for ([a (cdr (string-split (list-ref b 11) " "))] #:unless (equal? a "-")) (hash-set! axs a #t))
    (set! defs (append (parse-ranges (caddr (string-split (list-ref b 12) " "))) defs))
    (set! hyps (append (parse-ranges (cadr (string-split (list-ref b 13) " "))) hyps)))
  (define names (filter (lambda (a) (hash-ref axs a #f)) AXN))
  (define dd (remove-duplicates defs))
  (list (if (null? names) "ax -" (string-append "ax " (string-join names " ")))
        (if (null? dd) "def 0 -" (format "def ~a ~a" (length dd) (render-ranges dd)))
        (if (null? hyps) "hypent -" (string-append "hypent " (render-ranges hyps)))))

(define (main dir)
  (define segs (let loop ([k 1] [acc '()])
                 (define rel (format "book/J~a.txt" (pad k 6)))
                 (if (file-exists? (build-path dir rel)) (loop (add1 k) (cons rel acc)) (reverse acc))))
  (when (null? segs) (diff! "no book/J000001.txt under ~a" dir))
  ;; DUPLICATES rows: (pair kind src-id src-chain) -> (key booked_as)
  (define dups (make-hash))
  (for ([f (directory-list dir #:build? #t)] #:when (regexp-match? #rx"DUPLICATES[^/\\\\]*[.]tsv$" (path->string f)))
    (for ([ln (cdr (lines-of f))])
      (define c (split-tab ln))
      (define k (list (list-ref c 1) (list-ref c 0) (list-ref c 2) (list-ref c 3)))
      (when (hash-ref dups k #f) (diff! "DUPLICATES row twice: ~a" k))
      (hash-set! dups k (list (list-ref c 4) (list-ref c 5)))))
  (define used-dups (make-hash))
  (define head ZERO)
  (define next (make-hash))
  (define bkey (make-hash)) (define stmt-first (make-hash)) (define bkeys-by-id (make-hash))
  (define fkey-by-id (make-hash)) (define nkey-by-id (make-hash)) (define skey-by-id (make-hash))
  (define tot (make-hash)) (define proved 0) (define qualified 0)
  (define prev-rel #f)
  (for ([rel segs])
    (define lines (lines-of (build-path dir rel)))
    (define recs
      (for/list ([ln lines] [i (in-naturals 1)])
        (define fs (split-tab ln))
        (define body (drop-right fs 1)) (define ch (last fs))
        (define want (chain-of head (string-join body "\t")))
        (unless (equal? want ch) (diff! "~a line ~a: chain ~a, recomputed ~a" rel i ch want))
        (set! head ch)
        (define tag (car body)) (define kind (substring tag 0 1)) (define num (string->number (substring tag 1)))
        (unless (and num (equal? tag (id kind num))) (diff! "~a line ~a: bad id ~a" rel i tag))
        (unless (equal? num (hash-ref next kind 1)) (diff! "~a line ~a: ~a, expected number ~a" rel i tag (hash-ref next kind 1)))
        (hash-set! next kind (add1 (or num 0)))
        (define want-n (hash-ref #hash(("H" . 10) ("F" . 20) ("B" . 24) ("N" . 12) ("S" . 12) ("E" . 10)) kind #f))
        (unless (equal? want-n (length body)) (diff! "~a ~a: ~a fields, expected ~a" rel tag (length body) want-n))
        (cons body ch)))
    (define h (car (car recs))) (define e (car (last recs)))
    (unless (equal? (substring (car h) 0 1) "H") (diff! "~a: first record is not H" rel))
    (unless (equal? (substring (car e) 0 1) "E") (diff! "~a: last record is not E" rel))
    (unless (equal? (list-ref h 1) (string-append "segment " rel)) (diff! "~a: H names ~a" rel (list-ref h 1)))
    (unless (equal? (list-ref h 2) (if prev-rel (format "previous ~a ~a" prev-rel (sha256-file (build-path dir prev-rel))) "previous - -"))
      (diff! "~a: H previous field ~s" rel (list-ref h 2)))
    (define body-recs (drop-right (cdr recs) 1))
    (for ([r body-recs]) (when (member (substring (car (car r)) 0 1) '("H" "E")) (diff! "~a: ~a inside the segment" rel (car (car r)))))
    ;; E
    (define (rng k) (define ns (for/list ([r body-recs] #:when (equal? (substring (car (car r)) 0 1) k)) (string->number (substring (car (car r)) 1))))
      (if (null? ns) (string-append k " -") (format "~a-~a" (id k (car ns)) (id k (last ns)))))
    (unless (equal? (list-ref e 2) (format "records ~a" (sub1 (length recs)))) (diff! "~a: E ~a, segment has ~a before E" rel (list-ref e 2) (sub1 (length recs))))
    (for ([k '("F" "B" "N" "S")] [i '(3 4 5 6)]) (unless (equal? (list-ref e i) (rng k)) (diff! "~a: E field ~s, recomputed ~s" rel (list-ref e i) (rng k))))
    (unless (equal? (list-ref e 7) "C -") (diff! "~a: E C field ~a" rel (list-ref e 7)))
    ;; journal-level record checks
    (define fmap (make-hash)) ; master F id -> fields
    (define from-map (make-hash)) ; (kind src-id) -> (master-fields . chain)
    (define fbooked (make-hash)) ; master F id -> list of master B ids
    (for ([r body-recs])
      (define fs (car r)) (define tag (car fs)) (define kind (substring tag 0 1))
      (hash-update! tot kind add1 0)
      (define fr (regexp-match #px"^from ([A-Z][0-9]+) ([0-9a-f]{64})$" (last fs)))
      (if fr (let ([k (list kind (cadr fr))])
               (when (hash-ref from-map k #f) (diff! "~a: two records from source ~a" rel k))
               (hash-set! from-map k (cons fs (caddr fr))))
          (diff! "~a ~a: last field is not from <id> <chain>" rel tag))
      (case kind
        [("F") (hash-set! fmap tag fs) (hash-set! fkey-by-id tag (fld fs "sha256 ")) (hash-set! fbooked tag '())]
        [("B")
         (define f (hash-ref fmap (list-ref fs 1) #f))
         (cond
           [(not f) (diff! "~a ~a: F ~a not booked before it in this segment" rel tag (list-ref fs 1))]
           [else
            (hash-update! fbooked (list-ref fs 1) (lambda (l) (cons tag l)))
            (unless (equal? (list-ref fs 19) (string-append "pmp-verdict " (substring (list-ref f 8) 4))) (diff! "~a ~a: pmp-verdict differs from ~a" rel tag (car f)))
            (unless (equal? (list-ref fs 20) (string-append "racket-verdict " (substring (list-ref f 9) 7))) (diff! "~a ~a: racket-verdict differs from ~a" rel tag (car f)))
            (unless (equal? (list-ref fs 21) (list-ref f 10)) (diff! "~a ~a: verdicts differs from ~a" rel tag (car f)))
            (unless (equal? (list-ref fs 22) (list-ref f 16)) (diff! "~a ~a: receipt differs from ~a" rel tag (car f)))])
         (unless (string-prefix? (list-ref fs 8) "hyps ") (diff! "~a ~a: field 8" rel tag))
         (define st (list-ref fs 4))
         (cond [(equal? st "Proved") (set! proved (add1 proved)) (unless (equal? (list-ref fs 8) "hyps -") (diff! "~a ~a: Proved with hyps" rel tag))]
               [(equal? st "Qualified") (set! qualified (add1 qualified)) (when (equal? (list-ref fs 8) "hyps -") (diff! "~a ~a: Qualified without hyps" rel tag))]
               [else (diff! "~a ~a: status ~a" rel tag st)])
         (unless (regexp-match? #px"^pmp ACCEPT " (list-ref fs 17)) (diff! "~a ~a: no pmp ACCEPT" rel tag))
         (unless (regexp-match? #px"^racket ACCEPT " (list-ref fs 18)) (diff! "~a ~a: no racket ACCEPT" rel tag))
         (unless (regexp-match? #px"^pmp-verdict ACCEPT exit 0 " (list-ref fs 19)) (diff! "~a ~a: pmp-verdict is not ACCEPT exit 0" rel tag))
         (unless (regexp-match? #px"^racket-verdict ACCEPT exit 0 " (list-ref fs 20)) (diff! "~a ~a: racket-verdict is not ACCEPT exit 0" rel tag))
         (unless (regexp-match? #px"^receipt .+" (list-ref fs 22)) (diff! "~a ~a: no receipt" rel tag))
         (define stmt (fld fs "stmt ")) (define drv (fld fs "drv "))
         (define key (string-append stmt drv))
         (when (hash-ref bkey key #f) (diff! "~a ~a: same stmt and drv as ~a" rel tag (hash-ref bkey key)))
         (hash-set! bkey key tag) (hash-set! bkeys-by-id tag key)
         (define first (hash-ref stmt-first stmt #f))
         (unless first (hash-set! stmt-first stmt tag))
         (unless (equal? (list-ref fs 9) (if first (string-append "first " first) "first -")) (diff! "~a ~a: ~a, expected first ~a" rel tag (list-ref fs 9) (or first "-")))
         (unless (equal? (list-ref fs 10) "cites -")
           (for ([u (cdr (string-split (list-ref fs 10) " "))])
             (cond [(regexp-match? #px"^R[0-9]+$" u) (void)]
                   [(and (regexp-match? #px"^B[0-9]{7}$" u) (string<? u tag) (hash-ref bkeys-by-id u #f)) (void)]
                   [else (diff! "~a ~a: cite ~a is not an earlier posting" rel tag u)])))]
        [("N") (hash-set! nkey-by-id tag (fld fs "sha256 "))
               (unless (and (regexp-match? #px"^pmp REJECT " (list-ref fs 6)) (regexp-match? #px"^racket REJECT " (list-ref fs 7))) (diff! "~a ~a: not both REJECT" rel tag))
               (unless (regexp-match? #px"^receipt .+" (list-ref fs 9)) (diff! "~a ~a: no receipt" rel tag))]
        [("S") (hash-set! skey-by-id tag (fld fs "sha256 "))]
        [else (diff! "~a: unexpected ~a" rel tag)]))
    ;; F postings / booked counts
    (for ([(fid bl) fbooked])
      (define f (hash-ref fmap fid))
      (define ids (reverse bl))
      (define want (if (null? ids) "postings -" (format "postings ~a-~a" (car ids) (last ids))))
      (unless (equal? (list-ref f 11) want) (diff! "~a ~a: ~a, booked ~a" rel fid (list-ref f 11) want))
      (unless (null? ids)
        (define a (string->number (substring (car ids) 1)))
        (for ([b ids] [i (in-naturals)]) (unless (equal? b (id "B" (+ a i))) (diff! "~a ~a: postings not contiguous at ~a" rel fid b))))
      (define bk (regexp-match #px"^booked ([0-9]+) duplicates ([0-9]+)$" (list-ref f 18)))
      (cond [(not bk) (diff! "~a ~a: field 18 ~a" rel fid (list-ref f 18))]
            [else (unless (= (string->number (cadr bk)) (length ids)) (diff! "~a ~a: booked ~a, has ~a" rel fid (cadr bk) (length ids)))
                  (unless (= (+ (string->number (cadr bk)) (string->number (caddr bk))) (string->number (fld f "theorems "))) (diff! "~a ~a: booked + duplicates differ from theorems" rel fid))]))
    ;; ---------------------------------------------------------------- the sources
    (define pair (substring (list-ref h 6) 7))
    (define seg-dups (make-hash))
    (define matched (make-hash))
    (define (claim! k) (define v (hash-ref from-map k #f)) (when v (hash-set! matched k #t)) v)
    (define (source-files label field)
      (cond [(equal? field (string-append label " -")) '()]
            [(equal? pair "SHIPPED")
             (define m (regexp-match #px"^book (.+) segments ([0-9]+) head ([0-9a-f]{64}) records ([0-9]+)$" field))
             (if m (for/list ([k (in-range 1 (add1 (string->number (caddr m))))]) (path->string (build-path (cadr m) "book" (format "J~a.txt" (pad k 6)))))
                 (begin (diff! "~a: H ~a field ~s" rel label field) '()))]
            [else
             (define m (regexp-match #px"^[a-z]+ (.+) sha256 ([0-9a-f]{64}) head ([0-9a-f]{64}) records ([0-9]+)$" field))
             (cond [(not m) (diff! "~a: H ~a field ~s" rel label field) '()]
                   [(not (file-exists? (cadr m))) (diff! "~a: source ~a missing" rel (cadr m)) '()]
                   [else (unless (equal? (sha256-file (cadr m)) (caddr m)) (diff! "~a: source ~a sha256 differs from H" rel (cadr m)))
                         (list (cadr m))])]))
    ;; the shipped journal holds both parts; H field 9 says which part merged ("B PASS B…" / "N PASS N…" = merged;
    ;; anything else, e.g. "N PASS 1 of 2", was held by decide.rkt and must not be in the master). S goes with B.
    (define held (make-hash))
    (when (equal? pair "SHIPPED")
      (unless (regexp-match? #px"B PASS B[0-9]" (list-ref h 9)) (hash-set! held "B" #t))
      (unless (regexp-match? #px"N PASS N[0-9]" (list-ref h 9)) (hash-set! held "N" #t)))
    (define (check-source files field)
      (define m (regexp-match #px" head ([0-9a-f]{64}) records ([0-9]+)$" field))
      (define sh ZERO) (define sn 0)
      (define opened "-")
      (define bmap (make-hash)) ; source B id -> master B id
      (define cur-f #f) (define cur-bs '())
      (define (dup-of kind sid sch want-key key-of)
        (define d (hash-ref dups (list pair kind sid sch) #f))
        (cond [(not d) (diff! "~a: source ~a ~a neither booked nor in DUPLICATES" rel kind sid) #f]
              [else (hash-set! used-dups (list pair kind sid sch) #t)
                    (hash-update! seg-dups kind add1 0)
                    (unless (equal? (key-of (cadr d)) want-key) (diff! "~a: duplicate ~a ~a booked_as ~a has another key" rel kind sid (cadr d)))
                    (cadr d)]))
      (define (flush!)
        (when (and cur-f (hash-ref held "B" #f))
          ;; the shipped Book's accepted part was held: none of its F/B may be in the master
          (when (claim! (list "F" (car (car cur-f)))) (diff! "~a: held source ~a was booked" rel (car (car cur-f))))
          (for ([b cur-bs]) (when (claim! (list "B" (car (car b)))) (diff! "~a: held source ~a was booked" rel (car (car b)))))
          (set! cur-f #f) (set! cur-bs '()))
        (when cur-f
          (define f (car cur-f)) (define fch (cdr cur-f))
          (define bs (reverse cur-bs))
          (define mf (claim! (list "F" (car f))))
          (cond
            [mf
             (define mfs (car mf))
             (unless (equal? (cdr mf) fch) (diff! "~a ~a: from chain differs from source ~a" rel (car mfs) (car f)))
             (unless (equal? (take (cdr mfs) 10) (take (cdr f) 10)) (diff! "~a ~a: fields 1-10 differ from source ~a" rel (car mfs) (car f)))
             (define want-extra
               (if (equal? pair "SHIPPED")
                   (append (list "stmt -") (trace-union (map car bs)) (list (string-append "receipt " L9-VERDICTS (substring (list-ref f 10) 9)) (string-append "posted " opened)))
                   (take (list-tail f 12) 6)))
             (unless (equal? (take (list-tail mfs 12) 6) want-extra) (diff! "~a ~a: fields 12-17 differ from the source/derivation" rel (car mfs)))]
            [else (dup-of "F" (car f) fch (fld f "sha256 ") (lambda (m) (hash-ref fkey-by-id m #f)))])
          (for ([b bs])
            (define fs (car b)) (define sid (car fs))
            (define mb (claim! (list "B" sid)))
            (cond
              [mb
               (define mfs (car mb))
               (hash-set! bmap sid (car mfs))
               (unless (equal? (cdr mb) (cdr b)) (diff! "~a ~a: from chain differs from source ~a" rel (car mfs) sid))
               (unless (and mf (equal? (list-ref mfs 1) (car (car mf)))) (diff! "~a ~a: not under the master F of its source F" rel (car mfs)))
               (unless (equal? (take (list-tail mfs 2) 7) (take (list-tail fs 2) 7)) (diff! "~a ~a: fields 2-8 differ from source ~a" rel (car mfs) sid))
               (unless (equal? (take (list-tail mfs 11) 8) (take (list-tail fs 11) 8)) (diff! "~a ~a: fields 11-18 differ from source ~a" rel (car mfs) sid))
               (define want-cites
                 (if (equal? (list-ref fs 10) "cites -") "cites -"
                     (string-append "cites " (string-join (for/list ([u (cdr (string-split (list-ref fs 10) " "))])
                                                            (if (regexp-match? #px"^R" u) u (hash-ref bmap u (lambda () (diff! "~a ~a: source cite ~a unmapped" rel sid u) "?")))) " "))))
               (unless (equal? (list-ref mfs 10) want-cites) (diff! "~a ~a: cites ~s, mapped source cites ~s" rel (car mfs) (list-ref mfs 10) want-cites))]
              [else
               (define m (dup-of "B" sid (cdr b) (string-append (fld fs "stmt ") (fld fs "drv ")) (lambda (m) (hash-ref bkeys-by-id m #f))))
               (when m (hash-set! bmap sid m))]))
          (set! cur-f #f) (set! cur-bs '())))
      (for ([f files])
        (for-lines f
          (lambda (line)
            (define fs (split-tab line))
            (define body (drop-right fs 1)) (define ch (last fs))
            (define want (chain-of sh (string-join body "\t")))
            (unless (equal? want ch) (diff! "~a: source ~a chain differs at ~a" rel f (car body)))
            (set! sh ch) (set! sn (add1 sn))
            (define tag (car body)) (define kind (substring tag 0 1))
            (case kind
              [("H") (flush!) (set! opened (substring (list-ref body 3) 7))]
              [("F") (flush!) (set! cur-f (cons body ch))]
              [("B") (set! cur-bs (cons (cons body ch) cur-bs))]
              [("N" "S")
               (flush!)
               (define mr (claim! (list kind tag)))
               (cond
                 [(hash-ref held (if (equal? kind "S") "B" "N") #f)
                  (when mr (diff! "~a: held source ~a was booked" rel tag))]
                 [mr
                  (define mfs (car mr))
                  (unless (equal? (cdr mr) ch) (diff! "~a ~a: from chain differs from source ~a" rel (car mfs) tag))
                  (define want (if (= (length body) 11) (cdr body)
                                   (append (cdr body) (list (string-append "receipt " L9-VERDICTS (substring (list-ref body 8) 9)) (string-append "posted " opened)))))
                  (unless (equal? (take (cdr mfs) 10) want) (diff! "~a ~a: fields 1-10 differ from source ~a" rel (car mfs) tag))]
                 [else (dup-of kind tag ch (fld body "sha256 ") (lambda (m) (hash-ref (if (equal? kind "N") nkey-by-id skey-by-id) m #f)))])]
              [("C" "E") (flush!)]
              [else (diff! "~a: source record ~a" rel tag)]))))
      (flush!)
      (when m (unless (and (equal? sh (cadr m)) (= sn (string->number (caddr m)))) (diff! "~a: source head/records ~a ~a, H says ~a ~a" rel sh sn (cadr m) (caddr m)))))
    (define bfiles (source-files "book" (list-ref h 7)))
    (define nfiles (source-files "negative" (list-ref h 8)))
    (unless (null? bfiles) (check-source bfiles (list-ref h 7)))
    (unless (null? nfiles) (check-source nfiles (list-ref h 8)))
    ;; shipped: the shipped journal's N and S are in the book source; records from a part that was not merged would
    ;; show as "neither booked nor in DUPLICATES" above, so a SHIPPED segment must merge both parts or the checker says so
    (define want-d (format "duplicates F ~a B ~a N ~a S ~a" (hash-ref seg-dups "F" 0) (hash-ref seg-dups "B" 0) (hash-ref seg-dups "N" 0) (hash-ref seg-dups "S" 0)))
    (unless (equal? (list-ref e 9) want-d) (diff! "~a: E ~s, counted ~s" rel (list-ref e 9) want-d))
    (for ([(k v) from-map] #:unless (hash-ref matched k #f)) (diff! "~a: ~a names source record ~a, not found in its source" rel (car (car v)) k))
    (set! prev-rel rel)
    (printf "~a ~a records ~a\n" rel pair (length recs)) (flush-output))
  (for ([(k v) dups] #:unless (hash-ref used-dups k #f)) (diff! "DUPLICATES row not matched to a source record: ~a" k))
  (define (cnt k) (sub1 (hash-ref next k 1)))
  (printf "segments ~a records ~a\n" (length segs) (for/sum ([k '("H" "F" "B" "N" "S" "E" "C")]) (cnt k)))
  (printf "F ~a B ~a N ~a S ~a (Proved ~a, Qualified ~a); DUPLICATES rows ~a\n" (cnt "F") (cnt "B") (cnt "N") (cnt "S") proved qualified (hash-count dups))
  (printf "chain head ~a\n" head)
  (cond [(= problems 0) (printf "MASTER CHECK OK\n") 0]
        [else (printf "MASTER CHECK FAILED: ~a differences\n" problems) 1]))

(module+ main
  (define args (current-command-line-arguments))
  (unless (= (vector-length args) 1) (eprintf "usage: racket master-verify.rkt MASTERDIR\n") (exit 2))
  (exit (main (vector-ref args 0))))
