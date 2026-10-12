"""Independent exact Fraction and determinant-permutation oracle for the workbench."""
import argparse
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import time


def reduce_matrix(a, n):
    r = [row[:] for row in a]
    lead, pivots = 0, []
    for col in range(n):
        pivot = next((i for i in range(lead, len(r)) if r[i][col]), None)
        if pivot is None:
            continue
        r[lead], r[pivot] = r[pivot], r[lead]
        scale = r[lead][col]
        r[lead] = [x / scale for x in r[lead]]
        for i in range(len(r)):
            if i != lead:
                factor = r[i][col]
                r[i] = [x - factor * y for x, y in zip(r[i], r[lead])]
        pivots.append(col)
        lead += 1
        if lead == len(r):
            break
    return r, pivots


def determinant(a):
    n = len(a)
    total = Q(0)
    for perm in itertools.permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        term = Q(-1 if inversions % 2 else 1)
        for i, j in enumerate(perm):
            term *= a[i][j]
        total += term
    return total


def text(a, m, n):
    return f"rows: {m}\ncols: {n}\n" + ("\n".join(" ".join(map(str, row)) for row in a) if m * n else "")


def flat(a):
    return [str(x) for row in a for x in row]


def vectors(a):
    return [[str(x) for x in row] for row in a]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--engine", type=Path, required=True)
    parser.add_argument("--racket", default=r"C:\Program Files\Racket\racket.exe")
    args = parser.parse_args()
    out = Path(__file__).resolve().parent / ("run-" + time.strftime("%Y%m%d-%H%M%S"))
    out.mkdir(exist_ok=False)
    rng = random.Random(20261011)
    jobs, expected = [], {}

    def add(op, a, m, n, fields, b=None, bm=None, bn=None, suffix=""):
        ident = str(len(jobs)) + "-" + op + suffix
        job = {"id": ident, "op": op, "a": text(a, m, n)}
        if b is not None:
            job["b"] = text(b, bm, bn)
        jobs.append(job)
        expected[ident] = {"status": "ok", **fields}

    for m in range(5):
        for n in range(5):
            for sample in range(4):
                a = [[Q(rng.randint(-7, 7), rng.choice([1, 2, 3, 5])) for j in range(n)] for i in range(m)]
                if sample == 0:
                    a = [[Q(0) for j in range(n)] for i in range(m)]
                if sample == 1 and m > 1:
                    a[-1] = a[0][:]
                if sample == 3 and m and n:
                    a[0][0] = Q(10 ** 80 + 17, 10 ** 41 + 3)
                reduced, pivots = reduce_matrix(a, n)
                ker = []
                for free in set(range(n)) - set(pivots):
                    v = [Q(0)] * n
                    v[free] = Q(1)
                    for row, col in enumerate(pivots):
                        v[col] = -reduced[row][free]
                    ker.append(v)
                image = [[a[i][j] for i in range(m)] for j in pivots]
                rank_fields = {"rank": len(pivots), "nullity": n - len(pivots), "pivots": pivots}
                add("rref", a, m, n, {**rank_fields, "rows": m, "cols": n, "entries": flat(reduced)})
                add("rank", a, m, n, {**rank_fields, "kernel": vectors(ker), "image": vectors(image)})
                add("kernel", a, m, n, {**rank_fields, "kernel": vectors(ker)})
                add("image", a, m, n, {**rank_fields, "image": vectors(image)})
                transposed = [[a[i][j] for i in range(m)] for j in range(n)]
                add("transpose", a, m, n, {"rows": n, "cols": m, "entries": flat(transposed)})
                add("add", a, m, n, {"rows": m, "cols": n, "entries": flat([[2*x for x in row] for row in a])}, a, m, n)
                product = [[sum((a[i][k] * transposed[k][j] for k in range(n)), Q(0)) for j in range(m)] for i in range(m)]
                add("mul", a, m, n, {"rows": m, "cols": m, "entries": flat(product)}, transposed, n, m)
                x = [Q(rng.randint(-9, 9), 7) for _ in range(n)]
                b = [[sum((a[i][j]*x[j] for j in range(n)), Q(0))] for i in range(m)]
                aug, augp = reduce_matrix([a[i] + b[i] for i in range(m)], n + 1)
                particular = [Q(0)] * n
                for row, col in enumerate(augp):
                    particular[col] = aug[row][n]
                assert all(sum((a[i][j]*particular[j] for j in range(n)), Q(0)) == b[i][0] for i in range(m))
                assert all(not sum((a[i][j]*v[j] for j in range(n)), Q(0)) for v in ker for i in range(m))
                add("solve", a, m, n, {**rank_fields, "particular": list(map(str, particular)), "kernel": vectors(ker)}, b, m, 1)
                if m == n:
                    det = determinant(a)
                    add("det", a, m, n, {"determinant": str(det)})
                    if det:
                        inv_aug, _ = reduce_matrix([row + [Q(i == j) for j in range(n)] for i, row in enumerate(a)], 2*n)
                        inverse = [row[n:] for row in inv_aug]
                        add("inv", a, m, n, {"rows": n, "cols": n, "entries": flat(inverse), "rank": n, "determinant": str(det)})
                    else:
                        add("inv", a, m, n, {"status": "no-inverse", "rank": len(pivots), "determinant": "0"})

    add("solve", [[Q(1), Q(2)], [Q(2), Q(4)]], 2, 2, {"status": "inconsistent", "rank": 1, "nullity": 1}, [[Q(1)], [Q(3)]], 2, 1)
    for bad in ["[0.5]", "[1e3]", "[1/0]", "[1,2;3]", "rows: 1\ncols: 2\n1", "rows: -1\ncols: 0", "rows: 0\ncols: 2\n1 2", "empty 2 2"]:
        ident = str(len(jobs)) + "-invalid"
        jobs.append({"id": ident, "op": "rref", "a": bad})
        expected[ident] = {"status": "rejected"}
    jobs_path = out / "jobs.json"
    jobs_path.write_text(json.dumps(jobs) + "\n", encoding="utf-8")
    (out / "expected.json").write_text(json.dumps(expected, indent=2) + "\n")
    cmd = ([str(args.engine)] if args.engine.suffix == ".exe" else [args.racket, str(args.engine)]) + ["--batch", str(jobs_path)]
    started_hash = hashlib.sha256(args.engine.read_bytes()).hexdigest()
    result = subprocess.run(cmd, capture_output=True, timeout=120)
    (out / "stdout.json").write_bytes(result.stdout)
    (out / "stderr.txt").write_bytes(result.stderr)
    errors = []
    if result.returncode:
        errors.append({"process_exit": result.returncode, "error": result.stderr.decode(errors="replace")})
    else:
        actual = json.loads(result.stdout)
        assert len(actual) == len(jobs)
        for row in actual:
            want = expected[row["id"]]
            for field, value in want.items():
                if row["machine"].get(field) != value:
                    errors.append({"id": row["id"], "field": field, "expected": value, "actual": row["machine"].get(field)})
    report = {"cases": len(jobs), "command": cmd, "engine_sha256": started_hash, "mismatches": errors, "passed": not errors}
    (out / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    (out / "SHA256SUMS.txt").write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest()+"  "+p.name+"\n" for p in sorted(out.iterdir()) if p.is_file()))
    print(json.dumps({"output": str(out), "cases": len(jobs), "mismatches": len(errors), "sample": errors[:4]}))
    raise SystemExit(1 if errors else 0)


if __name__ == "__main__":
    main()
