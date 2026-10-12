#lang racket
;; Exact matrix arithmetic over the rationals.
;; Every stored number is an exact rational. A decimal or an exponent literal is rejected.
;; The 0 by 0 determinant is the empty product, 1. A particular solution sets each free variable to 0.

(provide (struct-out mat)
         (struct-out outcome)
         parse-matrix
         perform
         write-new-file
         rat->text
         outcome-exit-code
         self-check)

(struct mat (rows cols data) #:transparent)
(struct outcome (status text machine) #:transparent)

(define (rat->text q)
  (unless (and (rational? q) (exact? q))
    (error 'rat->text "refusing an inexact number"))
  (define n (numerator q))
  (define d (denominator q))
  (if (= d 1) (number->string n) (format "~a/~a" n d)))

(define (num-or-null x)
  (if (number? x) x 'null))

(define (finish status op reason updates)
  (define base
    (hash 'status status
          'op op
          'reason (or reason 'null)
          'rows 'null
          'cols 'null
          'entries 'null
          'rank 'null
          'nullity 'null
          'pivots 'null
          'determinant 'null
          'particular 'null
          'kernel 'null
          'image 'null
          'a_rows 'null
          'a_cols 'null
          'b_rows 'null
          'b_cols 'null))
  (for/fold ([h base]) ([(k v) (in-hash updates)])
    (hash-set h k v)))

(define (mat-entries-text m)
  (map rat->text (vector->list (mat-data m))))

(define (put-mat h m)
  (hash-set (hash-set (hash-set h 'rows (mat-rows m)) 'cols (mat-cols m)) 'entries (mat-entries-text m)))

(define (at data cols i j)
  (vector-ref data (+ (* i cols) j)))

(define (set-at! data cols i j v)
  (vector-set! data (+ (* i cols) j) v))

(define (swap-rows! data cols r1 r2)
  (unless (= r1 r2)
    (for ([j (in-range cols)])
      (define i1 (+ (* r1 cols) j))
      (define i2 (+ (* r2 cols) j))
      (define tmp (vector-ref data i1))
      (vector-set! data i1 (vector-ref data i2))
      (vector-set! data i2 tmp))))

(define (scale-row! data cols row s)
  (for ([j (in-range cols)])
    (define id (+ (* row cols) j))
    (vector-set! data id (* s (vector-ref data id)))))

(define (axpy! data cols dst src factor)
  (for ([j (in-range cols)])
    (define id (+ (* dst cols) j))
    (define is (+ (* src cols) j))
    (vector-set! data id (+ (vector-ref data id) (* factor (vector-ref data is))))))

(define (make-zero rows cols)
  (mat rows cols (make-vector (* rows cols) 0)))

(define (copy-data m)
  (vector-copy (mat-data m)))

;; Gauss-Jordan reduction. The pivot in a column is the first nonzero entry
;; at or below the current lead row. Returns the reduced matrix and the pivot columns.
(define (rref-data rows cols data)
  (define pivots '())
  (define lead 0)
  (for ([col (in-range cols)] #:break (= lead rows))
    (define prow
      (for/first ([i (in-range lead rows)]
                  #:when (not (zero? (at data cols i col))))
        i))
    (when prow
      (swap-rows! data cols prow lead)
      (define piv (at data cols lead col))
      (scale-row! data cols lead (/ 1 piv))
      (for ([i (in-range rows)] #:unless (= i lead))
        (define factor (at data cols i col))
        (unless (zero? factor)
          (axpy! data cols i lead (- factor))))
      (set! pivots (append pivots (list col)))
      (set! lead (add1 lead))))
  (values (mat rows cols data) pivots))

(define (rref-of m)
  (define data (copy-data m))
  (rref-data (mat-rows m) (mat-cols m) data))

(define (rank-of-pivots pivots)
  (length pivots))

(define (kernel-basis reduced pivots cols)
  (define pivot-set (list->set pivots))
  (define free (for/list ([j (in-range cols)] #:unless (set-member? pivot-set j)) j))
  (for/list ([f (in-list free)])
    (define v (make-vector cols 0))
    (vector-set! v f 1)
    (for ([row (in-naturals)] [pc (in-list pivots)])
      (vector-set! v pc (- (at (mat-data reduced) cols row f))))
    (vector->list v)))

(define (image-basis original pivots)
  (define rows (mat-rows original))
  (define cols (mat-cols original))
  (for/list ([pc (in-list pivots)])
    (for/list ([i (in-range rows)])
      (at (mat-data original) cols i pc))))

(define (augment m b)
  (define rows (mat-rows m))
  (define cols (mat-cols m))
  (define width (add1 cols))
  (define data (make-vector (* rows width) 0))
  (for ([i (in-range rows)])
    (for ([j (in-range cols)])
      (set-at! data width i j (at (mat-data m) cols i j)))
    (set-at! data width i cols (at (mat-data b) 1 i 0)))
  (mat rows width data))

(define (format-matrix m)
  (define rows (mat-rows m))
  (define cols (mat-cols m))
  (if (or (zero? rows) (zero? cols))
      (list (format "(empty matrix, ~a rows by ~a columns)" rows cols))
      (for/list ([i (in-range rows)])
        (string-join
         (cons "["
               (append (for/list ([j (in-range cols)])
                         (rat->text (at (mat-data m) cols i j)))
                       (list "]")))
         " "))))

(define (format-vectors vectors)
  (if (null? vectors)
      (list "(empty basis)")
      (for/list ([v (in-list vectors)] [k (in-naturals 1)])
        (format "~a. [ ~a ]" k (string-join (map rat->text v) " ")))))

(define (shape-sentence name m)
  (define rows (mat-rows m))
  (define cols (mat-cols m))
  (if (or (zero? rows) (zero? cols))
      (format "~a is an empty matrix with ~a rows and ~a columns." name rows cols)
      (format "~a is ~a by ~a." name rows cols)))

(define (ok-text lines)
  (string-join (cons "Exact result over the rational numbers." lines) "\n"))

(define (rejected-outcome op reason updates)
  (outcome "rejected"
           (string-append "Rejected. " reason)
           (finish "rejected" op reason updates)))

(define entry-re #px"^[+-]?[0-9]+(?:/[+-]?[0-9]+)?$")

(define (parse-entry tok where)
  (cond
    [(regexp-match? #px"[.eE]" tok)
     (error 'parse
            "The entry \"~a\" in ~a is not an integer or a rational fraction. Decimal points and exponent letters are rejected, and this workspace does not approximate."
            tok where)]
    [(not (regexp-match? entry-re tok))
     (error 'parse
            "The entry \"~a\" in ~a is not an integer or a rational fraction."
            tok where)]
    [else
     (define parts (string-split tok "/"))
     (define n (string->number (car parts)))
     (define d (if (null? (cdr parts)) 1 (string->number (cadr parts))))
     (unless (and (exact-integer? n) (exact-integer? d))
       (error 'parse "The entry \"~a\" in ~a did not parse as an exact integer." tok where))
     (when (zero? d)
       (error 'parse "A fraction cannot have denominator 0. The entry \"~a\" in ~a was rejected." tok where))
     (/ n d)]))

(define (split-rows body)
  (define chunks (regexp-split #px"[;\n]+" body))
  (filter (lambda (s) (not (regexp-match? #px"^\\s*$" s))) chunks))

(define (split-entries line)
  (filter non-empty-string? (regexp-split #px"[,[:space:]]+" (string-trim line))))

(define (parse-bracket-body body where)
  (define rows (split-rows body))
  (define parsed
    (for/list ([line (in-list rows)] [i (in-naturals 1)])
      (define toks (split-entries line))
      (when (null? toks)
        (error 'parse "Row ~a of ~a is empty." i where))
      (for/list ([tok (in-list toks)])
        (parse-entry tok (format "~a row ~a" where i)))))
  (when (null? parsed)
    (error 'parse "The bracket form of ~a has no rows. An empty matrix needs an explicit size, for example empty 0 3." where))
  (define cols (length (car parsed)))
  (for ([row (in-list parsed)] [i (in-naturals 1)])
    (unless (= (length row) cols)
      (error 'parse "Row ~a of ~a has ~a entries and row 1 has ~a entries." i where (length row) cols)))
  (mat (length parsed)
       cols
       (list->vector (apply append parsed))))

(define (parse-labeled text where)
  (define flat (regexp-replace* #px"\r\n|\r" text "\n"))
  (define lines (string-split flat "\n"))
  (define rows-n #f)
  (define cols-n #f)
  (define body-lines '())
  (for ([line (in-list lines)])
    (cond
      [(regexp-match? #px"^\\s*$" line) (void)]
      [(regexp-match? #px"(?i:rows|cols)\\s*:" line)
       (define matches (regexp-match* #px"(?i:(rows|cols))\\s*:\\s*([0-9]+)" line))
       (when (null? matches)
         (error 'parse "The dimension line \"~a\" in ~a is not a rows: or cols: declaration." (string-trim line) where))
       (define covered (regexp-replace* #px"(?i:(rows|cols))\\s*:\\s*[0-9]+" line ""))
       (unless (regexp-match? #px"^\\s*$" covered)
         (error 'parse "The dimension line \"~a\" in ~a also contains matrix entries. Put entries on their own lines." (string-trim line) where))
       (for ([whole (in-list matches)])
         (define km (regexp-match #px"(?i:(rows|cols))\\s*:\\s*([0-9]+)" whole))
         (define kind (string-downcase (cadr km)))
         (define n (string->number (caddr km)))
         (cond
           [(equal? kind "rows")
            (when rows-n (error 'parse "~a states rows more than once." where))
            (set! rows-n n)]
           [(equal? kind "cols")
            (when cols-n (error 'parse "~a states cols more than once." where))
            (set! cols-n n)]
           [else (error 'parse "Unknown dimension name in ~a." where)]))]
      [else (set! body-lines (append body-lines (list line)))]))
  (values rows-n cols-n (string-join body-lines "\n")))

(define (parse-matrix text [where "the matrix"])
  (define raw (if (string? text) text ""))
  (define trimmed (string-trim raw))
  (when (equal? trimmed "")
    (error 'parse "~a is empty. State the dimensions with rows: and cols:, with the bracket form [a, b; c, d], or with empty ROWS COLS." where))
  (define flat (regexp-replace* #px"\r\n|\r" trimmed "\n"))
  (cond
    [(regexp-match #px"(?i:^(empty|zero)\\s+([0-9]+)\\s+([0-9]+)\\s*$)" flat)
     => (lambda (m)
          (define r (string->number (caddr m)))
          (define c (string->number (cadddr m)))
          (when (and (equal? (string-downcase (cadr m)) "empty") (positive? r) (positive? c))
            (error 'parse "An empty matrix has zero rows or zero columns. Use zero ~a ~a for the zero matrix of that size." r c))
          (make-zero r c))]
    [(and (regexp-match? #px"^\\[" flat) (regexp-match? #px"\\]$" flat))
     (define inner (substring flat 1 (sub1 (string-length flat))))
     (when (regexp-match? #px"^\\s*$" inner)
       (error 'parse "The brackets in ~a do not state the dimensions. Use empty ROWS COLS, for example empty 0 3." where))
     (parse-bracket-body inner where)]
    [else
     (define-values (rows-n cols-n body) (parse-labeled flat where))
     (unless (and rows-n cols-n)
       (error 'parse "State the dimensions of ~a with rows: and cols:, or use the bracket form [a, b; c, d], or use empty ROWS COLS." where))
     (define row-lines (split-rows body))
     (cond
       [(or (zero? rows-n) (zero? cols-n))
        (when (pair? row-lines)
          (error 'parse "~a was declared empty (~a by ~a) and also contains entries." where rows-n cols-n))
        (make-zero rows-n cols-n)]
       [else
        (unless (= (length row-lines) rows-n)
          (error 'parse "~a declares ~a rows and the editor contains ~a nonempty rows." where rows-n (length row-lines)))
        (define parsed
          (for/list ([line (in-list row-lines)] [i (in-naturals 1)])
            (define toks (split-entries line))
            (unless (= (length toks) cols-n)
              (error 'parse "Row ~a of ~a has ~a entries and the stated column count is ~a." i where (length toks) cols-n))
            (for/list ([tok (in-list toks)])
              (parse-entry tok (format "~a row ~a" where i)))))
        (mat rows-n cols-n (list->vector (apply append parsed)))])]))

(define (with-parse op a-text b-text finish-ok)
  (with-handlers ([exn:fail? (lambda (e) (rejected-outcome op (exn-message e) (hash)))])
    (define A (parse-matrix a-text "matrix A"))
    (define B (if (and b-text (not (regexp-match? #px"^\\s*$" b-text)))
                  (parse-matrix b-text "matrix B")
                  #f))
    (finish-ok A B)))

(define (require-B B op A)
  (unless B
    (error 'parse "This operation uses matrix B, and the B editor is empty.")))

(define (dim-reject op reason A B)
  (rejected-outcome op reason
                    (hash 'a_rows (mat-rows A) 'a_cols (mat-cols A)
                          'b_rows (if B (mat-rows B) 'null)
                          'b_cols (if B (mat-cols B) 'null))))

(define (op-rref A)
  (define-values (R pivots) (rref-of A))
  (define rank (length pivots))
  (define nullity (- (mat-cols A) rank))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (format "The reduced row echelon form of A is shown below. The rank is ~a and the nullity is ~a." rank nullity)
                   (format "The pivot columns, counting from 0, are ~a." (if (null? pivots) "(none)" (string-join (map number->string pivots) ", "))))
             (format-matrix R)))
           (put-mat (finish "ok" "rref" #f
                            (hash 'rank rank 'nullity nullity 'pivots pivots
                                  'a_rows (mat-rows A) 'a_cols (mat-cols A)))
                    R)))

(define (op-rank A)
  (define-values (R pivots) (rref-of A))
  (define rank (length pivots))
  (define n (mat-cols A))
  (define nullity (- n rank))
  (define ker (kernel-basis R pivots n))
  (define im (image-basis A pivots))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (format "The rank is ~a and the nullity is ~a." rank nullity)
                   (format "Rank plus nullity equals the number of columns: ~a + ~a = ~a." rank nullity n)
                   "A basis of the kernel, one vector per line:" )
             (format-vectors ker)
             (list "A basis of the image, using the pivot columns of A:")
             (format-vectors im)))
           (finish "ok" "rank" #f
                   (hash 'rank rank 'nullity nullity 'pivots pivots
                         'kernel (map (lambda (v) (map rat->text v)) ker)
                         'image (map (lambda (v) (map rat->text v)) im)
                         'a_rows (mat-rows A) 'a_cols (mat-cols A)
                         'rows (mat-rows A) 'cols (mat-cols A)))))

(define (op-kernel A)
  (define-values (R pivots) (rref-of A))
  (define n (mat-cols A))
  (define ker (kernel-basis R pivots n))
  (define nullity (length ker))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (if (zero? nullity)
                       (format "The kernel contains only the zero vector in Q^~a. A basis of the kernel is empty." n)
                       (format "A basis of the kernel has ~a vectors in Q^~a." nullity n)))
             (format-vectors ker)))
           (finish "ok" "kernel" #f
                   (hash 'rank (length pivots) 'nullity nullity 'pivots pivots
                         'kernel (map (lambda (v) (map rat->text v)) ker)
                         'a_rows (mat-rows A) 'a_cols n))))

(define (op-image A)
  (define-values (R pivots) (rref-of A))
  (define im (image-basis A pivots))
  (define rank (length im))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (if (zero? rank)
                       (format "The image contains only the zero vector in Q^~a. A basis of the image is empty." (mat-rows A))
                       (format "A basis of the image has ~a vectors in Q^~a, taken from columns ~a of A, counting from 0."
                               rank (mat-rows A) (string-join (map number->string pivots) ", "))))
             (format-vectors im)))
           (finish "ok" "image" #f
                   (hash 'rank rank 'nullity (- (mat-cols A) rank) 'pivots pivots
                         'image (map (lambda (v) (map rat->text v)) im)
                         'a_rows (mat-rows A) 'a_cols (mat-cols A)))))

(define (op-solve A B)
  (require-B B "solve" A)
  (unless (= (mat-cols B) 1)
    (error 'parse
           "The system A x = b needs b to be a single column. Matrix B is ~a by ~a."
           (mat-rows B) (mat-cols B)))
  (unless (= (mat-rows A) (mat-rows B))
    (error 'parse
           "The system A x = b needs b to have one entry for each row of A. A is ~a by ~a and B is ~a by ~a."
           (mat-rows A) (mat-cols A) (mat-rows B) (mat-cols B)))
  (define-values (RA pivA) (rref-of A))
  (define ker (kernel-basis RA pivA (mat-cols A)))
  (define aug (augment A B))
  (define-values (RU pivU) (rref-of aug))
  (define rank-a (length pivA))
  (define inconsistent? (ormap (lambda (c) (= c (mat-cols A))) pivU))
  (define rank-u (length pivU))
  (if inconsistent?
      (outcome "inconsistent"
               (ok-text
                (append
                 (list (shape-sentence "A" A)
                       (format "Matrix B is ~a by 1." (mat-rows B))
                       (format "The system A x = b has no solution. The rank of A is ~a and the rank of the augmented matrix [A|b] is ~a."
                               rank-a rank-u)
                       "A basis of the kernel of A is shown because it is a basis of the solutions of A x = 0.")
                 (format-vectors ker)))
               (finish "inconsistent" "solve" "no solution"
                       (hash 'rank rank-a 'nullity (length ker) 'pivots pivA
                             'kernel (map (lambda (v) (map rat->text v)) ker)
                             'a_rows (mat-rows A) 'a_cols (mat-cols A)
                             'b_rows (mat-rows B) 'b_cols 1)))
      (let* ([n (mat-cols A)]
             [particular
              (let ([v (make-vector n 0)])
                (for ([row (in-naturals)] [pc (in-list pivU)])
                  (when (< pc n)
                    (vector-set! v pc (at (mat-data RU) (add1 n) row n))))
                (vector->list v))]
             [free (length ker)])
        (outcome "ok"
                 (ok-text
                  (append
                   (list (shape-sentence "A" A)
                         (format "Matrix B is ~a by 1." (mat-rows B))
                         (if (zero? free)
                             "The system A x = b has a unique solution. The particular solution is shown below. The homogeneous system A x = 0 has only the zero solution, so a basis of that solution space is empty."
                             (format "The system A x = b has infinitely many solutions. One particular solution, with each free variable set to 0, is shown below. A basis of the homogeneous solution space has ~a vectors." free))
                         (format "Particular solution: [ ~a ]" (string-join (map rat->text particular) " ")))
                   (list "Homogeneous basis:")
                   (format-vectors ker)))
                 (finish "ok" "solve" #f
                         (hash 'rank rank-a 'nullity free 'pivots pivA
                               'particular (map rat->text particular)
                               'kernel (map (lambda (v) (map rat->text v)) ker)
                               'a_rows (mat-rows A) 'a_cols (mat-cols A)
                               'b_rows (mat-rows B) 'b_cols 1))))))

(define (op-det A)
  (unless (= (mat-rows A) (mat-cols A))
    (error 'parse
           "The determinant is defined for a square matrix. A is ~a by ~a."
           (mat-rows A) (mat-cols A)))
  (define n (mat-rows A))
  (define data (copy-data A))
  (define det
    (let loop ([col 0] [acc 1])
      (cond
        [(= col n) acc]
        [else
         (define prow
           (for/first ([i (in-range col n)]
                       #:when (not (zero? (at data n i col))))
             i))
         (if (not prow)
             0
             (let ([sign (if (= prow col) 1 -1)])
               (swap-rows! data n prow col)
               (define piv (at data n col col))
               (for ([i (in-range (add1 col) n)])
                 (define factor (at data n i col))
                 (unless (zero? factor)
                   (axpy! data n i col (- (/ factor piv)))))
               (loop (add1 col) (* acc sign piv))))])))
  (outcome "ok"
           (ok-text
            (list (shape-sentence "A" A)
                  (if (and (zero? n) (= det 1))
                      "The determinant of the empty 0 by 0 matrix is 1."
                      (format "The determinant of A is ~a." (rat->text det)))))
           (finish "ok" "det" #f
                   (hash 'determinant (rat->text det)
                         'rows n 'cols n
                         'a_rows n 'a_cols n))))

(define (op-inv A)
  (unless (= (mat-rows A) (mat-cols A))
    (error 'parse
           "A matrix has an inverse only when it is square. A is ~a by ~a."
           (mat-rows A) (mat-cols A)))
  (define n (mat-rows A))
  (define det-text
    (let ([d (outcome-machine (op-det A))])
      (hash-ref d 'determinant)))
  (define aug (make-zero n (* 2 n)))
  (define data (mat-data aug))
  (for ([i (in-range n)])
    (for ([j (in-range n)])
      (set-at! data (* 2 n) i j (at (mat-data A) n i j)))
    (set-at! data (* 2 n) i (+ n i) 1))
  (define-values (R pivots) (rref-data n (* 2 n) data))
  (define full? (equal? pivots (build-list n values)))
  (if full?
      (let ([inv (make-zero n n)])
        (for ([i (in-range n)])
          (for ([j (in-range n)])
            (set-at! (mat-data inv) n i j (at (mat-data R) (* 2 n) i (+ n j)))))
        (outcome "ok"
                 (ok-text
                  (append
                   (list (shape-sentence "A" A)
                         (format "The inverse of A is shown below. The determinant of A is ~a." det-text))
                   (format-matrix inv)))
                 (put-mat (finish "ok" "inv" #f
                                  (hash 'determinant det-text 'rank n 'nullity 0
                                        'a_rows n 'a_cols n))
                          inv)))
      (outcome "no-inverse"
               (ok-text
                (list (shape-sentence "A" A)
                      (format "A has no inverse. A is ~a by ~a and its determinant is ~a." n n det-text)))
               (finish "no-inverse" "inv" "determinant is 0"
                       (hash 'determinant det-text 'rank (let-values ([(ra pa) (rref-of A)]) (length pa))
                             'a_rows n 'a_cols n 'rows n 'cols n)))))

(define (op-transpose A)
  (define rows (mat-rows A))
  (define cols (mat-cols A))
  (define out (make-zero cols rows))
  (for ([i (in-range rows)])
    (for ([j (in-range cols)])
      (set-at! (mat-data out) rows j i (at (mat-data A) cols i j))))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (format "The transpose of A is ~a by ~a and is shown below." cols rows))
             (format-matrix out)))
           (put-mat (finish "ok" "transpose" #f
                            (hash 'a_rows rows 'a_cols cols))
                    out)))

(define (op-add A B)
  (require-B B "add" A)
  (unless (and (= (mat-rows A) (mat-rows B)) (= (mat-cols A) (mat-cols B)))
    (error 'parse
           "The sum A + B is defined when A and B have the same number of rows and the same number of columns. A is ~a by ~a and B is ~a by ~a."
           (mat-rows A) (mat-cols A) (mat-rows B) (mat-cols B)))
  (define rows (mat-rows A))
  (define cols (mat-cols A))
  (define out (make-zero rows cols))
  (for ([k (in-range (* rows cols))])
    (vector-set! (mat-data out) k (+ (vector-ref (mat-data A) k) (vector-ref (mat-data B) k))))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (shape-sentence "B" B)
                   (format "The sum A + B is ~a by ~a and is shown below." rows cols))
             (format-matrix out)))
           (put-mat (finish "ok" "add" #f
                            (hash 'a_rows rows 'a_cols cols 'b_rows rows 'b_cols cols))
                    out)))

(define (op-mul A B)
  (require-B B "mul" A)
  (unless (= (mat-cols A) (mat-rows B))
    (error 'parse
           "The product A B is defined when the number of columns of A equals the number of rows of B. A is ~a by ~a and B is ~a by ~a."
           (mat-rows A) (mat-cols A) (mat-rows B) (mat-cols B)))
  (define m (mat-rows A))
  (define n (mat-cols A))
  (define p (mat-cols B))
  (define out (make-zero m p))
  (for ([i (in-range m)])
    (for ([j (in-range p)])
      (define sum
        (for/fold ([s 0]) ([k (in-range n)])
          (+ s (* (at (mat-data A) n i k) (at (mat-data B) p k j)))))
      (set-at! (mat-data out) p i j sum)))
  (outcome "ok"
           (ok-text
            (append
             (list (shape-sentence "A" A)
                   (shape-sentence "B" B)
                   (if (zero? n)
                       (format "The product A B is the ~a by ~a zero matrix, because the shared dimension is 0." m p)
                       (format "The product A B is ~a by ~a and is shown below." m p)))
             (format-matrix out)))
           (put-mat (finish "ok" "mul" #f
                            (hash 'a_rows m 'a_cols n 'b_rows n 'b_cols p))
                    out)))

(define (perform op a-text b-text)
  (define name
    (cond
      [(symbol? op) (symbol->string op)]
      [(string? op) op]
      [else "unknown"]))
  (define key (string->symbol name))
  (define proc
    (case key
      [(rref) (lambda (A B) (op-rref A))]
      [(rank) (lambda (A B) (op-rank A))]
      [(kernel) (lambda (A B) (op-kernel A))]
      [(image) (lambda (A B) (op-image A))]
      [(solve) (lambda (A B) (op-solve A B))]
      [(det) (lambda (A B) (op-det A))]
      [(inv) (lambda (A B) (op-inv A))]
      [(transpose) (lambda (A B) (op-transpose A))]
      [(add) (lambda (A B) (op-add A B))]
      [(mul) (lambda (A B) (op-mul A B))]
      [else #f]))
  (cond
    [(not proc)
     (rejected-outcome name (format "Unknown operation \"~a\"." name) (hash))]
    [else
     (with-handlers ([exn:fail?
                      (lambda (e)
                        (rejected-outcome name (exn-message e) (hash)))])
       (define A (parse-matrix (or a-text "") "matrix A"))
       (define needs-b? (memq key '(solve add mul)))
       (define B
         (cond
           [(and needs-b? b-text (not (regexp-match? #px"^\\s*$" b-text)))
            (parse-matrix b-text "matrix B")]
           [needs-b? #f]
           [else #f]))
       (proc A B))]))

(define (outcome-exit-code oc)
  (if (equal? (outcome-status oc) "rejected") 1 0))

(define (write-new-file path text)
  (define p (path->complete-path path))
  (when (or (file-exists? p) (directory-exists? p) (link-exists? p))
    (error 'export "Refusing to write ~a because that path already exists." p))
  (call-with-output-file p
    #:exists 'error
    (lambda (out) (write-string text out))))

(define (expect name ok?)
  (unless ok?
    (error 'self-check "~a failed" name)))

(define (self-check)
  (define A "rows: 2\ncols: 2\n0 1\n1 2\n")
  (define B "rows: 2\ncols: 1\n5\n7\n")
  (define d (perform 'det A ""))
  (expect "det -1" (equal? (hash-ref (outcome-machine d) 'determinant) "-1"))
  (define s (perform 'solve A B))
  (expect "solve" (equal? (hash-ref (outcome-machine s) 'particular) (list "-3" "5")))
  (define z (perform 'det "empty 0 0" ""))
  (expect "empty det" (equal? (hash-ref (outcome-machine z) 'determinant) "1"))
  (define bad (perform 'det "rows: 1\ncols: 1\n1.5\n" ""))
  (expect "decimal" (equal? (outcome-status bad) "rejected"))
  (define prod (perform 'mul "empty 2 0" "empty 0 3"))
  (expect "empty product rows" (equal? (hash-ref (outcome-machine prod) 'rows) 2))
  (expect "empty product cols" (equal? (hash-ref (outcome-machine prod) 'cols) 3))
  (expect "empty product entries" (equal? (hash-ref (outcome-machine prod) 'entries) (list "0" "0" "0" "0" "0" "0")))
  (define add-bad (perform 'add "rows: 1\ncols: 2\n1 2\n" "rows: 1\ncols: 1\n3\n"))
  (expect "add shape" (equal? (outcome-status add-bad) "rejected"))
  (define wide (perform 'solve "rows: 1\ncols: 2\n1 1\n" "rows: 1\ncols: 1\n3\n"))
  (expect "infinite status" (equal? (outcome-status wide) "ok"))
  (expect "kernel len" (= (length (hash-ref (outcome-machine wide) 'kernel)) 1))
  (define none (perform 'solve "rows: 2\ncols: 1\n1\n0\n" "rows: 2\ncols: 1\n0\n1\n"))
  (expect "inconsistent" (equal? (outcome-status none) "inconsistent"))
  #t)
