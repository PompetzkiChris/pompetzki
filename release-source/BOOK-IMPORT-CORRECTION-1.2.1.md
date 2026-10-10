# Book wrapper import spelling

The two corrected Book wrappers import `(file "portable-paths-r3.rkt")`. Their relative import resolves to the tested resolver in `1.2.1/book/delivered/code/portable-paths-r3.rkt`. The copied wrappers in `1.2.1/book/` also explicitly import that revision file. Independent inspection checked both imports and all six delivered checker files against the fresh release archive, with zero failures.

The opening paragraph of `1.2.1/SOURCE-CORRECTION-R2.md` described the import as `portable-paths.rkt`; the actual import names `portable-paths-r3.rkt`. This note supplies the exact spelling. The conventional `portable-paths.rkt` file in the delivered source directory is also byte-identical to the tested revision, but the wrappers explicitly load the revision name.

The complete active inventory for the selected version directory is `1.2.1/SOURCE-SHA256-R2.tsv`. This adjacent note is a separate Git blob. The original source files, preceding descriptions and manifests remain at their original paths.
