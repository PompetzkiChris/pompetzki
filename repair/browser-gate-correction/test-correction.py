#!/usr/bin/env python3
"""Run credited gate/API and judge-v5 wrapper checks into a fresh directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

BASE=Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interpreter",required=True)
    parser.add_argument("--wrapper",choices=("ps1","sh"),required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--judge-source",type=Path,help="Explicit JUDGE_V5 override for the override-route check")
    parser.add_argument("--powershell",default="pwsh")
    args=parser.parse_args()
    interpreter=shutil.which(args.interpreter)
    if not interpreter:
        raise FileNotFoundError("Supplied interpreter was not found: "+args.interpreter)
    judge=(args.judge_source or BASE.parents[1]/"judge/judge-v5.pmp").resolve(strict=True)
    expectations=json.loads((BASE/"TEST-CASES.json").read_text())
    for row in expectations:
        assert sha(BASE/row["path"])==row["sha256"]
    output=args.output.resolve()
    output.mkdir(parents=True,exist_ok=False)
    rows=[]

    def run(label,argv,expected_code,expected_gate=None,expected_accept=None,env=None,proof_expected=None):
        before=time.perf_counter()
        child=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env,timeout=60,creationflags=getattr(subprocess,"CREATE_NO_WINDOW",0))
        stdout=child.stdout.decode("utf-8",errors="replace")
        stderr=child.stderr.decode("utf-8",errors="replace")
        (output/(label+".stdout.txt")).write_bytes(child.stdout)
        (output/(label+".stderr.txt")).write_bytes(child.stderr)
        (output/(label+".exit.txt")).write_text(str(child.returncode)+"\n")
        gate="GATE" if stdout.startswith("GATE") else "REJECT" if stdout.startswith("REJECT registry") else "OTHER"
        passed=child.returncode==expected_code
        if expected_gate is not None:
            passed=passed and gate==expected_gate
        if expected_accept is not None:
            passed=passed and (("ACCEPT" in stdout)==expected_accept)
        invoked=None
        if proof_expected is not None:
            invoked=(output/(label+"-proof-invoked.txt")).exists()
            passed=passed and invoked==proof_expected
        row=dict(label=label,exit_code=child.returncode,timeout=False,seconds=time.perf_counter()-before,expected_exit=expected_code,expected_gate=expected_gate,observed_gate=gate,expected_accept=expected_accept,proof_invoked=invoked,passed=passed,stdout_file=label+".stdout.txt",stderr_file=label+".stderr.txt",stdout_sha256=hashlib.sha256(child.stdout).hexdigest(),stderr_sha256=hashlib.sha256(child.stderr).hexdigest(),unhandled_value_error="ValueError" in stderr)
        rows.append(row)
        return row

    run("api3538",[sys.executable,"-B",str(BASE/"test_api.py")],0)
    for case in expectations:
        if case["kind"]!="numeric-boundary":
            continue
        path=BASE/case["path"]
        expected_code=0 if case["gate"]=="GATE" else 1
        run("pmp-"+case["name"],[interpreter,str(BASE/"reggate.pmp"),str(path)],expected_code,case["gate"])
        run("python-"+case["name"],[sys.executable,"-B",str(BASE/"gate.py"),str(path)],expected_code,case["gate"])
    for case in expectations:
        if case["kind"]!="wrapper":
            continue
        label="wrapper-"+case["name"]
        env=dict(os.environ,POMPETZKI=interpreter,GATE_PROOF_LOG=str(output/(label+"-proof-invoked.txt")),PYTHONDONTWRITEBYTECODE="1")
        env.pop("JUDGE_V5",None)
        if case["name"]=="explicit-source-route":
            env["JUDGE_V5"]=str(judge)
        path=BASE/case["path"]
        if args.wrapper=="ps1":
            shell=shutil.which(args.powershell)
            if not shell:
                raise FileNotFoundError("Supplied PowerShell executable was not found")
            argv=[shell,"-NoLogo","-NoProfile","-File",str(BASE/"judge-gated.ps1"),"-Path",str(path)]
        else:
            argv=["sh",str(BASE/"judge-gated.sh"),str(path)]
        run(label,argv,case["exit"],case["gate"],case["accept"],env,case["proof_invoked"])
    summary=dict(schema="browser-gate-correction-tests/v1",wrapper=args.wrapper,python_version=sys.version.split()[0],python_integer_string_limit=getattr(sys,"get_int_max_str_digits",lambda:None)(),interpreter_filename=Path(interpreter).name,interpreter_sha256=sha(interpreter),judge_source_filename=judge.name,judge_source_sha256=sha(judge),cases=len(rows),passed=sum(r["passed"] for r in rows),failed=sum(not r["passed"] for r in rows),timeouts=0,api_checks=3538,numeric_boundary_executions=12,wrapper_executions=5,unhandled_value_errors=sum(r["unhandled_value_error"] for r in rows),source_hashes={p:sha(BASE/p) for p in ("gate.py","gate_core.py","embed_data.py","reggate.pmp","judge-gated.ps1","judge-gated.sh","test_api.py","test-correction.py")},rows=rows)
    (output/"results.json").write_text(json.dumps(summary,indent=2))
    with (output/"SHA256SUMS.txt").open("x",encoding="utf-8") as f:
        for path in sorted(output.iterdir()):
            if path.is_file() and path.name!="SHA256SUMS.txt":
                f.write(sha(path)+" *"+path.name+"\n")
    print(json.dumps({k:v for k,v in summary.items() if k!="rows"},indent=2))
    return 1 if summary["failed"] else 0

if __name__=="__main__":
    sys.exit(main())
