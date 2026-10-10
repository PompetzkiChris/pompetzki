# Delivered Book source mapping

`book/delivered/code/` contains the six corrected Book checker files copied byte for byte from the fresh, fully checked release archive. The two Racket wrappers resolve their relative `portable-paths.rkt` import within this corrected directory. Its conventional Python and Racket resolver names equal the explicit `verify-portable-r2.py` and `portable-paths-r3.rkt` implementations.

The preceding source commit retains earlier canonical filenames directly under `book/`. The new packaging builder already selects the corrected revision sources. This additional delivered-source directory makes direct wrapper execution use the same corrected resolver as the release archive.

For execution from the source checkout against an extracted Book asset:

```text
python book/delivered/code/verify-portable.py EXTRACTED_BOOK_ROOT
racket book/delivered/code/master-verify-portable.rkt EXTRACTED_BOOK_ROOT
racket book/delivered/code/master-verify-indep-portable.rkt EXTRACTED_BOOK_ROOT
```

`SOURCE-SHA256-R2.tsv` is the complete active source inventory. It includes the preceding manifest as a preserved source file and excludes only itself. Git blob byte checks bind the tagged commit to this inventory. The earlier source files, manifest and commit remain intact.
