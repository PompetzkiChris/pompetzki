"""Run repair/math-workbench-corrected/engine.rkt --batch on every applicable case and compare with the oracle."""
import json, subprocess, sys, collections
from oracle import *
ENGINE = '../../math-workbench-corrected/engine.rkt'
D = json.load(open('inputs/cases.json')); O = {r['id']: r for r in json.load(open('outputs/oracle.json'))['results']}
def mtext(X, m, n):
    if m == 0 or n == 0: return f"empty {m} {n}"
    return "[" + "; ".join(", ".join(r) for r in X) + "]"
jobs = []
for c in D['cases']:
    m, n, p = c['m'], c['n'], c['p']; a = mtext(c['A'], m, n)
    for op in ['rref', 'rank', 'kernel', 'image', 'transpose']: jobs.append(dict(id=f"{c['id']}:{op}", op=op, a=a))
    jobs.append(dict(id=f"{c['id']}:mul", op='mul', a=a, b=mtext(c['B'], n, p)))
    jobs.append(dict(id=f"{c['id']}:solve_consistent", op='solve', a=a, b=mtext([[v] for v in c['b_consistent']], m, 1)))
    if c['b_inconsistent']:
        jobs.append(dict(id=f"{c['id']}:solve_inconsistent", op='solve', a=a, b=mtext([[v] for v in c['b_inconsistent']], m, 1)))
    if m == n:
        jobs.append(dict(id=f"{c['id']}:det", op='det', a=a)); jobs.append(dict(id=f"{c['id']}:inv", op='inv', a=a))
json.dump(jobs, open('inputs/engine-jobs.json', 'w'), indent=1)
import os
cmd = json.loads(os.environ['POMPETZKI_MATRIX_ENGINE_COMMAND']) + ['--batch', 'inputs/engine-jobs.json']
pr = subprocess.run(cmd, capture_output=True, text=True)
open('logs/engine.stdout', 'w').write(pr.stdout); open('logs/engine.stderr', 'w').write(pr.stderr)
open('logs/engine.exit', 'w').write(f"{' '.join(cmd)}\nexit={pr.returncode}\n")
res = json.loads(pr.stdout)
json.dump(res, open('outputs/engine-results.json', 'w'), indent=1)
cases = {c['id']: c for c in D['cases']}
tally = collections.defaultdict(lambda: [0, 0]); fails = []
def grid(entries, rows, cols): return [[fparse(entries[i * cols + j]) for j in range(cols)] for i in range(rows)]
dec = lambda X: [[fparse(v) for v in r] for r in X]
for r in res:
    cid, op = r['id'].split(':'); c = cases[cid]; o = O[cid]; mc = r['machine']; m, n, p = c['m'], c['n'], c['p']
    A = dec(c['A']) if m else []
    if m and not n: A = [[] for _ in range(m)]
    try:
        ok = r['exit'] == 0 and mc.get('status') in ('ok', 'inconsistent', 'no-inverse')
        if op == 'rref': ok = ok and grid(mc['entries'], m, n) == dec(o['rref']) and mc['pivots'] == o['pivots']
        elif op == 'rank': ok = ok and mc['rank'] == o['rank'] and mc['nullity'] == o['nullity']
        elif op == 'kernel':
            K = dec(mc['kernel']); ok = ok and len(K) == o['nullity'] and all(all(v == 0 for v in matvec(A, k)) for k in K) and rank(K, n) == len(K)
        elif op == 'image':
            I = dec(mc['image']); ok = ok and len(I) == o['rank'] and rank(I, m) == o['rank'] and rank(transpose(A, n) + I, m) == o['rank']
        elif op == 'transpose': ok = ok and grid(mc['entries'], n, m) == dec(o['transpose'])
        elif op == 'mul': ok = ok and grid(mc['entries'], m, p) == dec(o['AB'])
        elif op == 'det': ok = ok and fparse(mc['determinant']) == fparse(o['det'])
        elif op == 'inv':
            if o['inverse'] is None: ok = ok and mc['status'] == 'no-inverse'
            else: ok = ok and mc['status'] == 'ok' and grid(mc['entries'], n, n) == dec(o['inverse'])
        elif op == 'solve_consistent':
            b = [fparse(v) for v in c['b_consistent']]; x = [fparse(v) for v in mc['particular']]
            K = dec(mc['kernel'])
            ok = ok and mc['status'] == 'ok' and matvec(A, x) == b and len(K) == o['nullity'] and all(all(v == 0 for v in matvec(A, k)) for k in K) and rank(K, n) == len(K)
        elif op == 'solve_inconsistent': ok = ok and mc['status'] == 'inconsistent' and mc['particular'] is None
    except Exception as e:
        ok = False; mc = dict(mc, _exception=repr(e))
    tally[op][0 if ok else 1] += 1
    if not ok: fails.append(dict(id=r['id'], category=c['category'], exit=r['exit'], machine=mc, text=r['text'][:400]))
json.dump(dict(command=' '.join(cmd), exit=pr.returncode, jobs=len(jobs), tally={k: dict(pass_=v[0], fail=v[1]) for k, v in tally.items()}, failures=fails),
          open('outputs/engine-compare.json', 'w'), indent=1)
print(f"engine exit={pr.returncode} jobs={len(jobs)}")
for k, v in sorted(tally.items()): print(f"  {k:20s} pass {v[0]:4d} fail {v[1]:4d}")
for f in fails[:20]: print("FAIL", f['id'], f['category'], f['exit'], str(f['machine'])[:300])
