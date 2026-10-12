#lang racket/gui
(require json racket/file racket/cmdline "package-utils.rkt" "../../math-workbench-v2/gui.rkt")
(define test-output #f)
(command-line #:program "MathWorkbench"
  #:once-each [("--ui-selftest") folder "Exercise the owned Compute control and save fresh answers" (set! test-output folder)]
  #:args () (void))
(cond
  [test-output
   (define output (path->complete-path test-output))
   (when (or (file-exists? output) (directory-exists? output)) (error 'MathWorkbench "test output already exists"))
   (make-directory* output)
   (define cases
     (list (list "rref-zero-pivot" 0 "[0,1;1,2]" "" "The reduced row echelon form")
           (list "rank-rectangular" 1 "[1,2,3;2,4,6]" "" "The rank is 1 and the nullity is 2")
           (list "solve-infinite" 4 "[1,2,3;2,4,6]" "[4;8]" "infinitely many solutions")
           (list "solve-inconsistent" 4 "[1,2;2,4]" "[1;3]" "no solution")
           (list "det-exact" 5 "[1/2,1/3;2/5,3/7]" "unused unfinished B" "17/210")
           (list "inverse-singular" 6 "[1,2;2,4]" "" "no inverse")
           (list "invalid-decimal" 0 "[0.5]" "" "Rejected")
           (list "empty-product" 9 "empty 2 0" "empty 0 3" "2 by 3 zero matrix")))
   (define results
     (for/list ([case cases])
       (define-values (name operation a b expected) (apply values case))
       (send a-text erase) (send a-text insert a)
       (send b-text erase) (send b-text insert b)
       (send op-choice set-selection operation)
       (send compute-button command (new control-event% [event-type 'button]))
       (define answer (answer-string))
       (call-with-output-file (build-path output (string-append name ".answer.txt")) #:exists 'error (lambda (out) (display answer out)))
       (unless (string-contains? answer expected) (error 'MathWorkbench "unexpected Answer for ~a: ~a" name answer))
       (hasheq 'case name 'answer answer 'expected_substring expected 'passed #t)))
   (change-font-size! 2) (change-font-size! -2)
   (define saved (build-path output "saved-answer.txt"))
   (save-answer-to saved)
   (define prior (file->bytes saved))
   (define refused? (with-handlers ([exn:fail? (lambda (e) #t)]) (save-answer-to saved) #f))
   (unless (and refused? (bytes=? prior (file->bytes saved))) (error 'MathWorkbench "existing output was not preserved"))
   (export-answer-to (build-path output "exported-answer.txt"))
   (define report (hasheq 'passed (length results) 'cases (length results) 'compute_control (send compute-button get-label)
                          'tests results 'answer_locked (send answer-text is-locked?) 'existing_save_refused refused?
                          'frame_shown (send frame is-shown?) 'runtime_modules (runtime-modules)
                          'interaction "Owned native Racket Compute control callback; no simulated input or focus changes"))
   (call-with-output-file (build-path output "results.json") #:exists 'error (lambda (out) (write-json report out)))
   (write-json report) (newline) (exit 0)]
  [else (send frame show #t)])
