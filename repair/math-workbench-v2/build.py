"""Portable build of the exact matrix GUI and CLI into a fresh directory."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--raco", default=shutil.which("raco"))
args = parser.parse_args()
if not args.raco:
    parser.error("provide --raco or put Racket's raco on PATH")
args.output.mkdir(parents=True, exist_ok=False)
source = Path(__file__).resolve().parent
suffix = ".exe" if os.name == "nt" else ""
for name, module, gui in [("MathWorkbench", "gui.rkt", True), ("MathEngine", "engine.rkt", False)]:
    command = [args.raco, "exe"] + (["--gui"] if gui else []) + ["-o", str(args.output/name) + suffix, str(source/module)]
    result = subprocess.run(command, capture_output=True)
    (args.output/(name+".build.stdout.txt")).write_bytes(result.stdout)
    (args.output/(name+".build.stderr.txt")).write_bytes(result.stderr)
    if result.returncode:
        raise SystemExit(result.returncode)
    print("built", args.output/(name+suffix))
