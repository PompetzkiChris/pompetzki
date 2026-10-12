#lang racket/gui
;; Native exact matrix workspace.
;; Matrix A, matrix B, the Compute control, and the Answer pane.
;; The frame stays hidden until main shows it, so a requiring module can call compute-now!.

(require "exact.rkt")

(provide frame
         a-text
         b-text
         answer-text
         op-choice
         compute-button
         change-font-size!
         compute-now!
         answer-string
         save-answer-to
         export-answer-to
         open-into)

(define op-symbols
  '(rref rank kernel image solve det inv transpose add mul))

(define op-labels
  '("RREF"
    "Rank and nullity"
    "Kernel basis"
    "Image basis"
    "Solve A x = b"
    "Determinant"
    "Inverse"
    "Transpose"
    "A + B"
    "A B"))

(define frame
  (new frame%
       [label "Pompetzki Math — Exact matrix workspace"]
       [width 1100]
       [height 760]))

(define root (new vertical-panel% [parent frame] [spacing 6] [border 8]))
(new message% [parent root] [label "Rank-Nullity: The First Isomorphism Theorem"])
(new message% [parent root] [label "Enter integers or fractions. A maps Q^n to Q^m; Compute displays the exact answer."])

(define controls
  (new horizontal-panel%
       [parent root]
       [stretchable-height #f]
       [spacing 8]
       [alignment '(left center)]))

(define op-choice
  (new choice%
       [parent controls]
       [label "Operation"]
       [choices op-labels]
       [stretchable-width #f]))

(define a-text (new text%))
(define b-text (new text%))
(define answer-text (new text%))
(define font-size 16)
(define (apply-font! editor)
  (define locked? (send editor is-locked?))
  (send editor lock #f)
  (define delta (make-object style-delta% 'change-size font-size))
  (send delta set-delta-face "Consolas")
  (send editor change-style delta 0 (send editor last-position))
  (send editor lock locked?))
(define (change-font-size! step)
  (set! font-size (min 40 (max 10 (+ font-size step))))
  (for ([editor (list a-text b-text answer-text)]) (apply-font! editor)))

(define (answer-string)
  (send answer-text get-text))

(define (set-answer s)
  (send answer-text lock #f)
  (send answer-text erase)
  (send answer-text insert s)
  (apply-font! answer-text)
  (send answer-text lock #t))

(define (compute-now!)
  (define idx (send op-choice get-selection))
  (define op (list-ref op-symbols idx))
  (define oc (perform op (send a-text get-text) (send b-text get-text)))
  (set-answer (outcome-text oc))
  oc)

(define compute-button (new button%
     [parent controls]
     [label "Compute"]
     [callback (lambda (button event) (compute-now!))]))
(new button% [parent controls] [label "Font −"] [callback (lambda (b e) (change-font-size! -2))])
(new button% [parent controls] [label "Font +"] [callback (lambda (b e) (change-font-size! 2))])

(define editors (new horizontal-panel% [parent root] [spacing 8]))

(define (editor-column parent title editor)
  (define col (new vertical-panel% [parent parent] [spacing 4]))
  (new message% [parent col] [label title])
  (new editor-canvas%
       [parent col]
       [editor editor]
       [min-width 300]
       [min-height 240]
       [style '(auto-hscroll auto-vscroll)])
  col)

(editor-column editors "Matrix A" a-text)
(editor-column editors "Matrix B or b (Add, Multiply, Solve)" b-text)
(editor-column editors "Answer" answer-text)
(send answer-text lock #t)

(define (open-into editor)
  (define path (get-file "Open a matrix" frame))
  (when path
    (with-handlers ([exn:fail? (lambda (e) (set-answer (exn-message e)))])
      (define contents (file->string path))
      (send editor lock #f)
      (send editor erase)
      (send editor insert contents)
      (apply-font! editor))))

(define (save-answer-to path)
  (write-new-file path (answer-string)))

(define (export-answer-to path)
  (define payload
    (string-join
     (list "Exact matrix workspace export"
           "operation:"
           (list-ref op-labels (send op-choice get-selection))
           "matrix A:"
           (send a-text get-text)
           "matrix B:"
           (send b-text get-text)
           "answer:"
           (answer-string))
     "\n"))
  (write-new-file path payload))

(define (choose-new-file title writer)
  (define path (put-file title frame))
  (when path
    (with-handlers ([exn:fail? (lambda (e) (set-answer (exn-message e)))])
      (writer path)
      (set-answer (string-append "Wrote " (path->string path) "\n\n" (answer-string))))))

(define menu-bar (new menu-bar% [parent frame]))
(define file-menu (new menu% [label "File"] [parent menu-bar]))
(new menu-item% [label "Open into A..."] [parent file-menu] [callback (lambda (i e) (open-into a-text))])
(new menu-item% [label "Open into B..."] [parent file-menu] [callback (lambda (i e) (open-into b-text))])
(new menu-item% [label "Save answer..."] [parent file-menu] [callback (lambda (i e) (choose-new-file "Save answer" save-answer-to))])
(new menu-item% [label "Export answer..."] [parent file-menu] [callback (lambda (i e) (choose-new-file "Export answer" export-answer-to))])

(send a-text insert "rows: 2\ncols: 2\n0 1\n1 2\n")
(send b-text insert "rows: 2\ncols: 1\n5\n7\n")
(for ([editor (list a-text b-text answer-text)]) (apply-font! editor))

(module+ main
  (send frame show #t))
