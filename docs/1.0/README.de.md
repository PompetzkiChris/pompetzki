# Abschluss 1.0

Abschluss ist ein System für Mathematiker, die maschinengeprüfte Mathematik als Bücher führen, von Christopher Pompetzki. Dies ist Release 1.0.0 (Tag `v1.0.0`) von `PompetzkiChris/pompetzki`, 2026-10-10.

Der Name steht für den Buchhaltungsabschluss und für den Abschluss einer Menge. Gute Beweise sind gute Buchführung und gutes Abschließen.

## Was Abschluss ist

| Teil | Was es ist |
|---|---|
| Das Cockpit, `Abschluss.exe` | Bücher im ERP-Stil für maschinengeprüfte Mathematik unter Windows x64, geschrieben in pmp. Jede Aktion ist ein Klick. |
| Die Sprache pmp | Christopher Pompetzkis exakte Sprache der linearen Algebra. `pompetzki.exe` (Windows) und `pompetzki` (statisches Linux x86-64) sind ihre Interpreter. Ganze Zahlen sind exakt. |
| Der pmp-Prüfer, `judge-v3.pmp` | Prüft Herleitungen in einem Hilbert-Kalkül für Logik erster Stufe mit Gleichheit über ZF: die Funktion `check_batch` in `rocq/Replay2.v`. Eingabeformat: JDG1. |
| Der zweite Prüfer in Racket, `racket/judge.rkt` | Eine unabhängige Implementierung derselben Funktion, geschrieben nach dem Text der Regeln. |
| Das Hauptbuch des Book, `lib/ledger.pmp` | Das Hauptbuch des Book: Tabellen, Statusregeln, Wesentlichkeit, Altersstruktur, Saldenliste, Kosten. |

### Das Cockpit

Das Cockpit führt die Bücher so, wie ein Buchhalter sie führt.

- **Konten.** Hauptbuch: Lean-4-Projekte. Nebenbücher: **Computed** (berechnet, C) und **Certified** (zertifiziert, K) aus pmp-Process-Protokollen, **Proved** (bewiesen, P) aus Rocq-Prüfungen. Der Tokenverbrauch der Modelle ist das Geld.
- **Belege.** Ein Beleg je Quellereignis, jeder mit einer Nummer:

  | Art | Buchstabe | Einer je |
  |---|---|---|
  | Lean-Commit | G | Commit, der `.lean`-Dateien ändert |
  | pmp-Lauf | K (mit Behauptungen) oder C (ohne) | `==== run`-Block in einem Process-Protokoll |
  | Rocq-Prüfung | P | Prüfauftrag |
  | Stornierung | R | Stornierung |
  | Periodenabschluss | A | abgeschlossene Periode |

- **Status.** Jeder Status ist ein Wort und eine Farbe: Closed (abgeschlossen), Certified, Proved (grün); Computed, Checked (geprüft), Reversed (storniert) (grau); Unpriced (unbewertet), Qualified (eingeschränkt), Annotation (Anmerkung), Impaired (wertgemindert) (gelb); Open (offen), Rejected (abgelehnt), Incomplete (unvollständig), Error (Fehler) (rot). Eine Zeile ist erst grün, wenn ein Kernel oder eine pmp-Regel sie akzeptiert hat.
- **Bildschirme.** Der Entwurf nennt 13: Cockpit (Aufgaben mit Ampeln), Journal, Document (Beleg), General ledger (Hauptbuch), Open items (Offene Posten, mit Wesentlichkeit, Alter und Altersklassen 0–7, 8–30, 31–90, über 90 Tage), Trial balance (Saldenliste), Axioms (Axiome), Bill of materials (Stückliste), Costs (Kosten), Vendors (Lieferanten), Jobs (Aufträge), Periods (Perioden), Settings (Einstellungen). Jede Zahl führt bis zu den Quellzeilen zurück, aus denen sie entsteht. Bisher gebaut: Plan 1, jedes konfigurierte pmp-Process-Protokoll als Belege gelesen (Journal, Document, Open items, Trial balance), jede Zahl gleich dem Zertifikat des Laufs und durch eine unabhängige Lesung in Racket bestätigt; Plan 2, Jobs, Run again (erneut ausführen) und der Rocq-Prüfauftrag; Plan 3, Stornierung, Periodenabschluss, Export, Periods und Settings.
- **Periodenabschluss.** Schließt den frühesten offenen Monat des Projekts; Monate werden der Reihe nach geschlossen, und nur beendete Monate. Er schreibt `ledger\periods\<project>-<yyyymm>.txt`: die Saldenliste, die Aufgaben mit ihren Ampeln, jede Belegnummer mit dem sha256 ihrer Quelle, die Stornierungen, die Namen der Interpreter und die Konfigurationsdatei. Er ist mit Angabe des Grundes gesperrt, solange eine Aufgabe rot ist. Belege einer geschlossenen Periode erscheinen gesperrt.
- **Stornierungen.** Der Grund wird aus einer Liste von fünf gewählt (falsche Aussage, falsches Zertifikat, ersetzt, durch Gegenbeispiel widerlegt, Lauf irrtümlich), mit einer optionalen Notiz. Die Stornierung ist eine neue Datei in `ledger\reversals\`; der Beleg erhält den Status Reversed.
- **Exporte.** Das aktuelle Raster als neue TSV-Datei in `exports\`.
- **Nichts wird überschrieben.** Das Cockpit öffnet jede Datei, die es schreibt, mit `CREATE_NEW`. Korrekturen sind Stornobelege. Das Speichern der Einstellungen schreibt eine neue `config\config-<yyyymmddhhmmss>.txt`; die neueste gilt.

Das Cockpit liest und berichtet. Es bucht pmp-Behauptungen noch nicht nach Lean. Entwurf: `docs/specs/2026-09-27-cockpit-design.md`.

## Was der Download enthält

| Datei | Inhalt |
|---|---|
| `Abschluss-1.0-windows-x64.zip` | das Cockpit, der pmp-Interpreter und -Prüfer, der Racket-Prüfer, der Selbsttest, Beispiele und Werkzeuge |
| `Abschluss-1.0-source.zip` | die Quellen |
| `Abschluss-1.0-results.zip` | die Ergebnisse und ihre Belege |
| `SHA256SUMS.txt` | der SHA-256 jeder Datei |

Frühere Releases im selben Repository:

- `v2026.10.10`, das Release des pmp-Prüfers: <https://github.com/PompetzkiChris/pompetzki/releases/tag/v2026.10.10>
- `deadline-snapshot-20261010`, ein Vorab-Release (Prerelease) mit dem Arbeitsstand zu diesem Zeitpunkt:
  <https://github.com/PompetzkiChris/pompetzki/releases/tag/deadline-snapshot-20261010>

## Installation

<!--OPTIONAL:installer-->
`Install-Abschluss.exe` ausführen.

Oder `Abschluss-1.0-windows-x64.zip` in einen Ordner entpacken und `Abschluss.exe` von dort starten.

Der Racket-Prüfer benötigt Racket (`racket.exe`).

## Download prüfen

Windows (cmd oder PowerShell), im Download-Ordner:

```
certutil -hashfile Abschluss-1.0-windows-x64.zip SHA256
```

Den ausgegebenen Hash mit der Zeile für diese Datei in `SHA256SUMS.txt` vergleichen.

Linux oder WSL:

```
sha256sum -c SHA256SUMS.txt --ignore-missing
```

<!--OPTIONAL:verifier-->
`abschluss-verify.exe` prüft die heruntergeladenen Dateien gegen `SHA256SUMS.txt`.

## Selbsttest

<!--OPTIONAL:selftest-->
`selftest.cmd` unter Windows oder `selftest.sh` unter Linux und WSL ausführen. Eine Datei, die die Prüfer akzeptieren, gibt `ACCEPT` (akzeptiert) aus und endet mit 0; eine abgelehnte Datei gibt `REJECT` (abgelehnt) mit Satz und Schritt aus und endet mit 1.

Der Lauf des Prüfers über den Replay von Satz 29, von Hand, steht in `QUICKSTART.md`.

## Was bewiesen ist

- **Der Prüfer ist korrekt.** In Rocq 9.1.0, mit coqchk `Axioms: <none>`: `check_batch` akzeptiert nur herleitbare Sätze (`rocq/Replay3.v`: `check_thm_ok`, `check_batch_ok`; Register `RpInitOk.REG0_ok`). Also ist `check_batch` korrekt bezüglich `prov`.
- **Zwei unabhängige Prüfer stimmen überein.** Der pmp-Prüfer und der Racket-Prüfer geben beide ACCEPT aus:
  - der Replay von Satz 29, `replay-all.jdg`: Con(ZFC) → Con(ZFC + ¬CH\*), 4.551 Sätze, 139.194 Schritte;
  - die Σ₁-Dateien der Stufe 2 (Arithmetik von ω als ZF-Sätze): 7 Dateien, 1.656 Sätze, 53.069 Schritte.
- **Mutanten werden abgelehnt.** Jede ausprobierte mutierte Kopie, darunter die 70 Mutanten der Σ₁-Dateien, wird von beiden Prüfern mit REJECT abgelehnt.

Nicht behauptet:

- Dass die Bytes von `judge-v3.pmp`, unter der pmp-Semantik ausgeführt, `check_batch` berechnen. Der Rocq-Beweis ist offen und geschuldet. Bis er abgeschlossen ist, beruht ein pmp-Urteil auf seiner Übereinstimmung mit der Racket-Kopie.
- Die Unabhängigkeit von CH über ZFC. Satz 29 ist Cohens Hälfte. Gödels Hälfte, über L, ist geschuldet; sie ist in Rocq, vom Kernel geprüft, auf die Verpflichtungen O1–O11 zurückgeführt.

## Was geschuldet ist

Die zehn Stufen des Ausbaus. Die Stufen 1–8 sind so, wie in `v2026.10.10` veröffentlicht; die Stufen 9 und 10 schließen dieses Release ein.

| # | Stufe | Geliefert | Geschuldet |
|---|---|---|---|
| 1 | Prüfer v0 und sein Rocq-Satz | `check_batch` korrekt bezüglich `prov` (Replay3, coqchk none); Gam → ZFpure für reine Formeln (CX3); `judge/mut` von beiden Prüfern abgelehnt | der Rocq-Satz, dass die Bytes von `judge-v3.pmp`, unter der pmp-Semantik ausgeführt, `check_batch` berechnen |
| 2 | Σ₁-Vollständigkeit und abgeleitete Regeln | Σ₁-Vollständigkeit in Rocq; Arithmetik von ω; LRAT, Smith, Rang-Kern-Satz (rank–nullity), Pratt, Farkas gebucht | Gröbner und Nullstellensatz über den Prüfer gebucht |
| 3 | Racket-Kopie | fertig; stimmt bei jeder Datei überein | — |
| 4 | Nativer Prüfer-Abzug | `bin/linux/jdgchk` | der Rocq-Satz über die Bytes des Abzugs (x86-64-Semantik) |
| 5 | Metamath set.mm | Registerabbildung der klassenfreien Kohorte | Import der Beweise aus set.mm; Export ins Metamath-Format |
| 6 | Lean/Mathlib | 252 Aussagen als ZF-Sätze, neu hergeleitet | Übersetzung von Lean-Beweistermen; Int; Universen als unerreichbare Kardinalzahlen |
| 7 | Automatisierung | 6 Emitter, 1 in pmp geschrieben | die übrigen Emitter als pmp-Programme |
| 8 | Die 5090 | Rang / Kern / Smith über `extern` | die anderen Zertifikatsfamilien auf der GPU |
| 9 | Das Book in pmp | `lib/ledger.pmp`; Cockpit-Pläne 1–3 | das Hauptbuch und der Arbeitsplatz, verbunden mit den Buchungen des Prüfers |
| 10 | Öffentliches Release | `v2026.10.10`; dieses Release | — |

Ebenfalls geschuldet:

- Die Lean-Seite (AbschlussCore, Buchungen der Agenten) liegt auf Lean v4.28.0, das 3 bekannte Kernel-Exploits hat. Jede solche Buchung trägt den Vermerk „Replay auf einem korrigierten Kernel geschuldet“.
- Gödels Hälfte von CH (Verpflichtungen O1–O11).

Die vollständige Liste, mit den eigenen offenen Punkten des Cockpits und den Plattformgrenzen: `KNOWN-LIMITS.md`.

## Weiteres

- `QUICKSTART.md`: die ersten zehn Minuten.
- `CHANGELOG.md`: was sich geändert hat, Release für Release.
- `KNOWN-LIMITS.md`: was geschuldet ist und was noch nicht funktioniert.

## Lizenz

Der originale Code und die Dokumentation von Pompetzki: MIT (`LICENSE`), Copyright Christopher Pompetzki. Material Dritter behält seine Lizenz: Metamath set.mm CC0-1.0, Lean und Mathlib Apache-2.0.

Die Methode (exakte lineare Algebra, ein Zertifikat je Lauf, das Prinzip der endlichen Daten (Finite Data Principle), Satz 21.1) stammt von Christopher Pompetzki.

<!-- Übersetzung von docs/README.md (sha256 48d93749399d6021586baf6e2e556db62b2b07cc412212fba2ff92b2a94004a1) durch GitHub Copilot; bei Abweichungen gilt die englische Fassung. -->

