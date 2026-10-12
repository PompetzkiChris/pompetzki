# Abschluss 1.3.1 Windows packaging

The portable launcher opens the editable exact Math Workbench by default. Its
menu retains the cockpit, authenticated pmp judge with independent Racket
cross-check, verified Book posting and current posting verification, historical
Book chain verification, documentation, and file manifest checking.

Build prerequisites are Python, Racket with `raco`, NASM, and MinGW-w64 GCC.
The installed application includes its Racket runtime and DLLs. These tools are
required to rebuild the source; they are not required to use the Windows ZIP.

From the extracted source package, build into a new directory:

```
python repair/packaging/v9-judge-v6-1.3.1/build-bundle.py --rebuild-core --output NEW_BUILD_DIRECTORY
```

The included `vendor` directory contains the audited 1.2 Windows base ZIP,
its SHA256, the tested native gate, and its finite test/provenance receipts.
The build reconstructs the fixed interpreter from the included NASM source,
rebuilds the native gate from its frozen pmp source, and compares its allocated
PE sections against the tested gate. It compiles and distributes the native
Racket applications and re-emits the cockpit from its included portable source.

In the candidate checkout, the audited inputs can be supplied explicitly:

```
python repair/packaging/v9-judge-v6-1.3.1/build-bundle.py --base-zip AUDITED_ZIP --base-checksums AUDITED_SHA256SUMS --cockpit-source AUDITED_SOURCE_DIRECTORY --native-dir VERIFIED_NATIVE_DIRECTORY --runtime-dir VERIFIED_RUNTIME_DIRECTORY --source-map FROZEN_V6_RUNTIME_V2_SOURCE_MAP --raco RACO_EXECUTABLE --output NEW_BUILD_DIRECTORY
```

Every build output directory is new. Each command has preserved stdout,
stderr, arguments, working directory, exit status, and timing in `logs` and
`commands.json`. `build-receipt.json` records input and component hashes.
The Windows ZIP includes `MANIFEST.sha256`; the source ZIP verifies all frozen
authoritative source mappings and includes the interpreter ASM, native compiler,
Book v7 code, corrected exact workbench, and independent Fraction oracle.
Judge v6 rejects count fields exceeding necessary remaining-input byte bounds
before array allocation. Book v7 uses the recorded hash-bound judge route for
fresh rejudgment. The Matrix v2 and runtime v2 sources remain selected through
their frozen manifests.

The source archive selects cockpit code and mathematical helpers through
`COCKPIT-SOURCE-MANIFEST.json`. It excludes historical journals, digests,
conversation instructions, local configuration and the Chrome DevTools client.
`SUPPORT-SOURCE-MANIFEST.json` selects fixtures, certificate evidence and library
test inputs. Packaging files themselves are selected by an explicit public
manifest; additional working files are excluded.

`Install Abschluss.exe --target NEW_DIRECTORY --no-shortcut` installs only
into a new target with existing non-reparse parents. The default GUI creates a
Start Menu shortcut. `Uninstall Abschluss.exe --dry-run` lists the installation
receipt. Uninstallation checks each listed file against its installation hash,
removes only matching listed files, and preserves additional files, modified
files, and links. Directory removals are limited to empty recorded directories.

`test-package.py` extracts fresh ZIPs, restricts PATH to Windows, sets an empty
Racket collection directory, invokes native owned GUI callbacks while hidden,
runs 849 independent exact Fraction cases, judges true/false/forged inputs,
posts/checks and relocates Book postings, verifies both installation routes,
refuses existing targets and junction parents, and tests recorded-file removal.
All shortcut tests use a test-owned APPDATA directory. The tests use no
simulated keystrokes, focus changes, or controls from other applications.
The receipts cover actual callbacks and resulting Answer text. Windows remain
hidden throughout these tests.

The earlier failed build and test directories remain as evidence. Release
publishing is performed by the parent task after its remaining release checks.

The package test driver reads its JSON and text receipts explicitly as UTF-8.
UTF8-VALIDATION-CORRECTION.json identifies the preserved earlier decoder failure.
