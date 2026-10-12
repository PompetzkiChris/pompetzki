#!/usr/bin/env python3
"""Run the reviewed v5 certificate corpus with explicitly supplied checker paths."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import csv
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
FAMILIES = ("bot-semantic", "bot-malformed", "numeric", "math", "replay")
FAST = frozenset(("bot-semantic", "bot-malformed", "numeric"))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def executable(name):
    found = shutil.which(name)
    if found is None:
        raise FileNotFoundError("Executable lookup failed for supplied checker/tool: " + name)
    return str(Path(found).resolve())

def classify(raw, timeout):
    if timeout:
        return "TIMEOUT", "timeout"
    text = raw.decode("latin-1")
    verdict = next((s.strip().split()[0] for s in text.splitlines() if re.match(r"^(ACCEPT|REJECT|LIMIT)\b", s.strip())), "OTHER")
    if verdict == "ACCEPT":
        return verdict, "accept"
    if verdict != "REJECT":
        return verdict, "other"
    if "initial registry" in text:
        return verdict, "registry"
    parser_messages = ("does not begin with JDG1", "R expected", "T expected", "text after the last theorem", "does not end in white space", "more than 12", "a number was expected", "ends where a tag was expected", "unknown formula tag", "unknown step tag", "parse error")
    if any(s in text for s in parser_messages):
        return verdict, "parser"
    final_messages = ("no lines", "last line is not the statement", "sig repeats", "not closed", "hypothesis used", "final:")
    if any(s in text for s in final_messages):
        return verdict, "final-statement"
    return verdict, "proof-step"

def arguments():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="New output directory; existing directories are refused")
    parser.add_argument("--native", help="Standalone native checker executable or PATH name")
    parser.add_argument("--interpreter", help="pmp interpreter executable or PATH name; requires --pmp-source")
    parser.add_argument("--pmp-source", type=Path, help="pmp judge source for the supplied interpreter")
    racket = parser.add_mutually_exclusive_group()
    racket.add_argument("--racket-source", type=Path, help="Racket judge source; uses --racket-executable")
    racket.add_argument("--racket-standalone", help="Standalone Racket checker executable or PATH name")
    parser.add_argument("--racket-executable", default="racket", help="Racket executable or PATH name for --racket-source")
    parser.add_argument("--lane", choices=("fast", "full"), default="fast", help="fast selects 136 bot/numeric cases; full selects all 254")
    parser.add_argument("--interpreted-lane", choices=("fast", "full"), default="fast", help="Filter interpreted executions independently; default omits 117 math cases and full replay")
    parser.add_argument("--families", nargs="+", choices=FAMILIES, help="Additional family filter within the selected lane")
    parser.add_argument("--case", action="append", dest="cases", help="Additional exact case-ID filter; may repeat")
    parser.add_argument("--timeout", type=int, default=180, help="Per-execution timeout in seconds")
    parser.add_argument("--jobs", type=int, default=4, help="Concurrent checker processes")
    args = parser.parse_args()
    if not any((args.native, args.interpreter, args.racket_source, args.racket_standalone)):
        parser.error("Supply at least one checker route")
    if bool(args.interpreter) != bool(args.pmp_source):
        parser.error("--interpreter and --pmp-source must be supplied together")
    if args.timeout <= 0 or args.jobs <= 0:
        parser.error("--timeout and --jobs must be positive")
    return args

def main():
    args = arguments()
    expectation_path = BASE / "expectations.tsv"
    expectations = list(csv.DictReader(expectation_path.open(encoding="utf-8", newline=""), delimiter="\t"))
    if len(expectations) != 254 or len({r["case"] for r in expectations}) != 254:
        raise ValueError("Reviewed expectation set must contain 254 distinct cases")
    requested = set(args.cases or [])
    unknown = requested - {r["case"] for r in expectations}
    if unknown:
        raise ValueError("Unknown case IDs: " + ", ".join(sorted(unknown)))
    selected = [r for r in expectations if (args.lane == "full" or r["family"] in FAST) and (not args.families or r["family"] in args.families) and (not requested or r["case"] in requested)]
    if not selected:
        raise ValueError("Filters select no cases")
    for row in selected:
        path = BASE / row["file"]
        if sha(path) != row["sha256"]:
            raise ValueError("Corpus hash differs from reviewed expectation: " + row["case"])
    routes = {}
    runtime_inputs = []

    def route(name, command, labels):
        routes[name] = (command, labels)
        for label, path in zip(labels, command):
            runtime_inputs.append(dict(route=name, role=label, filename=Path(path).name, sha256=sha(path)))

    if args.native:
        route("native", [executable(args.native)], ["NATIVE_CHECKER"])
    if args.interpreter:
        route("interpreted", [executable(args.interpreter), str(args.pmp_source.resolve(strict=True))], ["PMP_INTERPRETER", "PMP_SOURCE"])
    if args.racket_source:
        route("racket", [executable(args.racket_executable), str(args.racket_source.resolve(strict=True))], ["RACKET_EXECUTABLE", "RACKET_SOURCE"])
    elif args.racket_standalone:
        route("racket", [executable(args.racket_standalone)], ["RACKET_STANDALONE"])
    jobs = [(kind, row) for kind in routes for row in selected if kind != "interpreted" or args.interpreted_lane == "full" or row["family"] in FAST]
    if not jobs:
        raise ValueError("Filters leave no executions for the supplied checker routes")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    order = {r["case"]:i for i,r in enumerate(expectations)}

    def run(job):
        kind, row = job
        command, labels = routes[kind]
        argv = command + [str(BASE / row["file"])]
        start = time.perf_counter()
        timeout = False
        try:
            child = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=args.timeout)
            stdout, stderr, code = child.stdout, child.stderr, child.returncode
        except subprocess.TimeoutExpired as exc:
            stdout, stderr, code, timeout = exc.stdout or b"", exc.stderr or b"", None, True
        folder = output / kind
        folder.mkdir(exist_ok=True)
        stem = f"{order[row['case']]:03d}-{row['sha256'][:12]}"
        stdout_path = folder / (stem + ".stdout.txt")
        stderr_path = folder / (stem + ".stderr.txt")
        stdout_path.write_bytes(stdout)
        stderr_path.write_bytes(stderr)
        (folder / (stem + ".exit.txt")).write_text(str(code) + "\n", encoding="utf-8")
        verdict, cls = classify(stdout, timeout)
        expected_exit = int(row["expected_exit"])
        return dict(judge=kind, case=row["case"], family=row["family"], input_file=row["file"], input_sha256=row["sha256"], command_roles=labels+[row["file"]], expected_verdict=row["expected_verdict"], expected_exit=expected_exit, expected_class=row["expected_class_"+kind], verdict=verdict, cls=cls, exit_code=code, timeout=timeout, seconds=time.perf_counter()-start, stdout_file=stdout_path.relative_to(output).as_posix(), stderr_file=stderr_path.relative_to(output).as_posix(), stdout_sha256=hashlib.sha256(stdout).hexdigest(), stderr_sha256=hashlib.sha256(stderr).hexdigest(), passed=(not timeout and verdict==row["expected_verdict"] and code==expected_exit and cls==row["expected_class_"+kind]))

    before = time.perf_counter()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(run, jobs))
    (output / "results.json").write_text(json.dumps(rows, indent=2), encoding="utf-8")
    fields = ("judge", "case", "family", "expected_verdict", "expected_exit", "expected_class", "verdict", "exit_code", "cls", "timeout", "passed", "stdout_sha256", "stderr_sha256")
    with (output / "results.tsv").open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields, delimiter="\t", extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    summary = dict(schema="portable-v5-validation-run/v1", lane=args.lane, interpreted_lane=args.interpreted_lane, families=args.families, selected_cases=len(selected), runs=len(rows), passed=sum(r["passed"] for r in rows), failed=sum(not r["passed"] for r in rows), timeouts=sum(r["timeout"] for r in rows), seconds=time.perf_counter()-before, expectations_sha256=sha(expectation_path), driver_sha256=sha(Path(__file__)), runtime_inputs=runtime_inputs, by_judge={kind:dict(runs=sum(r["judge"]==kind for r in rows), passed=sum(r["judge"]==kind and r["passed"] for r in rows)) for kind in routes}, failures=[{k:r[k] for k in ("judge","case","expected_verdict","expected_class","verdict","cls","exit_code","timeout")} for r in rows if not r["passed"]], command_path_policy="Recorded commands use explicit role names and package-relative corpus paths; runtime input filenames and hashes identify the supplied artifacts.")
    (output / "summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    with (output / "SHA256SUMS.txt").open("x", encoding="utf-8") as f:
        for p in sorted(output.rglob("*")):
            if p.is_file() and p.name != "SHA256SUMS.txt":
                f.write(sha(p) + " *" + p.relative_to(output).as_posix() + "\n")
    print(json.dumps(summary, indent=2))
    return 1 if summary["failed"] else 0

if __name__ == "__main__":
    sys.exit(main())
