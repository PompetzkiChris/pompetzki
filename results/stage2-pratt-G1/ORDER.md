# G1 (Grok Build, Area-51): Pratt primality certificate corpus for lane L2D

Rules: `C:\ClaudeOutput\pompetzki\lanes\RULES-ROUND2-2026-10-09.md`.

**Context.** Lane L2D (`C:\ClaudeOutput\pompetzki\lanes\L2D\`, read-only for you) turns certificates into judge derivations: rank, Smith, Farkas, LRAT and Pratt. Read its `cert-*.rkt` and `certs*.rkt` files to learn the Pratt format it expects. If it has none yet, write `FORMAT.md` with your format and follow it exactly.

**Task.**
1. In Racket with exact integers, write a Pratt certificate generator and a separate, independent checker. A certificate for a prime p gives:
   - a witness a with a^(p-1) ≡ 1 (mod p);
   - the full factorization of p-1;
   - a^((p-1)/q) ≢ 1 (mod p) for every prime factor q;
   - recursive certificates for each q.
2. Build the corpus:
   - every prime below 10^6;
   - the primes 2^31-1, 2^61-1 and 2^89-1, the first 30 Fermat-type primes p = k·2^n+1 below 2^64, and the 10 largest primes below 2^64.
   - For each prime: certificate, certificate size in bytes, recursion depth, generation and check times in integer ms.
3. Negative controls: for 1,000 composites, including Carmichael numbers and strong pseudoprimes to bases 2 and 3, show that no certificate passes. Mutate 1,000 certificates (wrong witness, wrong factor, dropped factor) and show the checker rejects every one.
4. Hand-off for L2D: an index file listing, per prime, the certificate path and its sha256.

**Output:** in `C:\ClaudeOutput\pompetzki\lanes\G1-pratt\`:
- the generator, the checker and the corpus;
- `INDEX.tsv`;
- RESULTS.md and STATUS.txt.
