# Windows folder and uninstall correction

The released 1.3.1 helper was reproduced on Windows with a child environment lacking APPDATA and an owned recorded shortcut. It exited 1 with a null Path argument after removing unchanged payloads and the receipt, while the shortcut remained. The original reproduction and its source hashes remain under `repair/appdata-owned-windows-20261012-013202`.

Version 1.3.2 uses explicit nonempty absolute APPDATA and LOCALAPPDATA paths when supplied. Absent or empty variables use Windows Programs and LocalApplicationData folder lookup. Racket and PowerShell reject relative and drive-relative explicit paths. The folder query is checked against the actual Windows APIs; test runs never write the user's Programs directory.

Uninstall now resolves and checks shortcut eligibility before changing payloads. A path error occurs during preflight, with payloads and the receipt retained. Recorded hash, shortcut target, Programs containment and reparse checks remain. A shortcut outside the resolved Programs directory remains preserved. Modified and additional files remain preserved.

The original correction draft passed 20 of 21 owned cases; its Racket path resolver accepted a drive-relative path which PowerShell refused. The corrected source and its independent versioned checks pass all 21 cases: 11 path-resolution cases and ten uninstall cases. Parent environment variables remain unchanged. The v11 documentation hash mismatch and partial build outputs remain beside the new v12 recipe.

The frozen v12 recipe selects 23 payload files plus its source manifest. Its three product corrections derive from the checked v10 copies with only active version literals changed to 1.3.2. The matrix, v6 judge, interpreter, Book v7 and their source selectors retain their reviewed bytes. Both package and source-only builds pass 76 package checks including 849 exact matrix cases and eight owned hidden GUI callbacks, plus 40 count checks with zero timeouts. The 11 source-closure checks pass, all 417 ordinary files match, and the source ZIP reproduces byte for byte.

`validation-1.3.2-public.zip` supplies the explicit finite test subset, selected raw logs, source and byte receipts, correction driver and compact Windows case records. Two profile-path raw outputs remain local; the archive names the omissions. Physical visible-window clicks and full native/compiler/OS/whole-judge correspondence remain separate acceptance obligations.
