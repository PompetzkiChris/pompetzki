# Exact independent matrix validation

The Grok Bot linear-algebra lane supplied the Python Fraction oracle, a seeded corpus of 429 matrices, and independent identity predicates. `SOURCE-CREDIT.json` binds the received archive. Codex added a fresh output-directory driver and an explicit engine command. Earlier delivered files and Windows reruns are preserved separately.

The tests compare RREF, rank and nullity, kernel and image bases, transpose, multiplication, Ax=b solutions, inconsistent systems, determinant and inverse. They include zero dimensions, singular matrices and numerators/denominators beyond 64-bit words. Determinants are checked with elimination, Bareiss and permutation formulas for the smaller matrices. Deliberately wrong basis and solution controls check the comparison predicates.

From an installed Windows bundle, run:

```text
python verify.py --output "fresh matrix results" --engine "PATH/TO/bin/MathEngine.exe"
```

With Racket source, provide the interpreter and engine source as the two arguments following `--engine`. The driver records code hashes, the supplied engine hashes, subprocess output and exit status, an exact SHA-256 list, and the comparison results. Expectations use integers and exact rational numbers with exact zero decisions.
