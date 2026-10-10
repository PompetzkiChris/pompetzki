# Portable checker correction

The corrected release asset is built with `package-book-r2.py`, `verify-portable-r2.py` and `portable-paths-r3.rkt`. Earlier source files and predecessor archives remain at their earlier paths. This correction supplies new source files and a new archive stage.

The earlier Python checker confined manifest paths but could follow a `CERTIFICATES.tsv` or `PATH-ALIASES.tsv` path outside the archive root. The earlier Racket resolver could fall back to an original absolute provenance path when its alias was absent. A synthetic outside-root payload demonstrated a false portable-check success; that fixture makes no mathematical judgment claim.

The corrected Python checker confines every mapped path, requires manifest membership and binds every admitted F/N record to its certificate, alias, digest and size. The corrected Racket resolver confines mapped paths, rejects links/junctions and rejects absent historical aliases, including Windows drive paths when executed on Linux. A probe for the next absent journal segment remains permitted so that the source-record checkers can detect the end of the chain.

Both corrected implementations reject absolute escapes, parent traversal, contained payloads omitted from the manifest and absent historical aliases. Both accept a valid contained payload and the absent-next-journal probe. The Python rejection checks remain active under `python -O`.

The delivered archive contains the corrected implementations under both their explicit revision names and the conventional entry-point names used by its full source-record checkers. From the extracted package root, run:

```text
python code/verify-portable-r2.py .
racket code/master-verify-portable.rkt .
racket code/master-verify-indep-portable.rkt .
```

To perform safe archive extraction followed by all three checks, `verify-archive-r2.py` accepts an archive path, a new extraction directory and a new receipt directory. It checks ZIP member containment, duplicate names, symlink entries and CRCs before extraction.

The journal, original 33-segment prefix, admitted payloads, counts and source decisions are unchanged by this checker correction. Final archive checks and exact hashes are provided in the release receipt asset.
