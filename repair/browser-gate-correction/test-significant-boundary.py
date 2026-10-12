"""Check the exact 12/13-significant-digit boundary in the two gate sources."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

BASE=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--interpreter",required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    output=args.output.resolve()
    output.mkdir(parents=True,exist_ok=False)
    cases=[("twelve-significant","999999999999","formula"),("thirteen-significant","1000000000000","parse")]
    rows=[]
    for name,value,reason in cases:
        path=output/(name+".jdg")
        path.write_text("JDG1 R 1 a a i a b e 0 "+value+" e 0 1 q 1 0 0 T 0\n",encoding="ascii")
        for kind,command in (("pmp",[args.interpreter,str(BASE/"reggate.pmp")]),("python",[sys.executable,"-B",str(BASE/"gate.py")])):
            child=subprocess.run(command+[str(path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60,creationflags=getattr(subprocess,"CREATE_NO_WINDOW",0))
            stem=name+"-"+kind
            (output/(stem+".stdout.txt")).write_bytes(child.stdout)
            (output/(stem+".stderr.txt")).write_bytes(child.stderr)
            text=child.stdout.decode("utf-8",errors="replace")
            rows.append(dict(case=name,implementation=kind,expected_reason=reason,exit_code=child.returncode,passed=child.returncode==1 and text.startswith("REJECT registry") and reason in text.splitlines(),stdout_sha256=hashlib.sha256(child.stdout).hexdigest(),stderr_sha256=hashlib.sha256(child.stderr).hexdigest()))
    summary=dict(runs=4,passed=sum(r["passed"] for r in rows),failures=sum(not r["passed"] for r in rows),rows=rows)
    (output/"results.json").write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2))
    return 1 if summary["failures"] else 0

if __name__=="__main__":
    sys.exit(main())
