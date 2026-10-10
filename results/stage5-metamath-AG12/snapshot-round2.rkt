#lang racket/base
(require "round2-core.rkt" racket/file racket/list racket/path racket/string)
(define original-names
  (string-split
   "CLASS-FREE.tsv COVERAGE.tsv EXTENSION-FORMULAS-v2.tsv EXTENSION-FORMULAS.tsv EXTENSION-VERIFY.tsv INVENTORY.tsv LOGIC-BOOLEAN-CHECK.rkt LOGIC-BOOLEAN-CHECK.tsv LOGIC-MATCHES.tsv LOGIC-ROUTES.rkt LOGIC-ROUTES.tsv LOGIC-SOURCE-UNION.tsv LOGIC-SOURCE.rkt MAP-SUMMARY.tsv MAP.tsv MATCH-ANALYSIS.md MATCH-VALIDATION.tsv ORDER-2.md ORDER.md REGISTRY.tsv RESULTS.md RUN-BY.txt SET-CANDIDATES.tsv SET-DERIVATION-SOURCES.md SET-EXTENSION-PROTOTYPES.tsv SET-MATCH-ANALYSIS.md SHA256.tsv SOURCE-LABELS.tsv SOURCE-SHA256.tsv STATUS.txt VERIFY-FINAL.tsv extension-formulas-v2.rkt extension-formulas.rkt extension-verify-v2.rkt extension-verify-v3.rkt extension-verify-v4.rkt extension-verify.rkt inventory-v2.rkt inventory-v3.rkt inventory-v4.rkt inventory.rkt launch.end.txt launch.start.txt launch2.start.txt make-map-v2.rkt make-map.rkt mm-extension-existence.rkt mm-extension-inspect.rkt registry-correction-01.rkt registry-correction-02.rkt registry-reader-v2.rkt registry-reader-v3.rkt registry-reader.rkt set-candidate-writer.rkt set-extension-prototypes.rkt verify-final.rkt write-report-v2.rkt write-report-v3.rkt write-report.rkt"))
(new-table "ORIGINALS-SHA256-2.tsv" '("path" "bytes" "sha256" "mtime_epoch_seconds")
           (map sha-record (sort original-names string<?)))
(displayln (format "Captured ~a original files; launcher logs excluded." (length original-names)))
