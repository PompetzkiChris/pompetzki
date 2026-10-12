"""Build the included Pompetzki NASM source into a new output directory.

Copyright (c) 2026 Christopher Pompetzki. See LICENSE for the MIT license.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EXPECTED_SOURCE_SHA256 = "778a2710b4151bad5a71c1bbdf5b5243d86d01f2a654fd727f341d589f2289db"

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def tool(name):
    found = shutil.which(name)
    if not found:
        raise RuntimeError(f"Build tool was not found on PATH: {name}")
    return found

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="New output directory")
    parser.add_argument("--source", type=Path, default=ROOT / "source" / "pompetzki.asm")
    parser.add_argument("--target", choices=("windows", "linux"), default="windows" if os.name == "nt" else "linux")
    parser.add_argument("--nasm", default="nasm")
    parser.add_argument("--windows-linker", default="gcc", help="MinGW-w64 GCC on Windows or a cross GCC on Linux")
    parser.add_argument("--linux-linker", default="ld")
    parser.add_argument("--allow-modified-source", action="store_true", help="Build a source revision and record its new hash")
    args = parser.parse_args()
    source = args.source.resolve(strict=True)
    source_hash = sha(source)
    if source_hash != EXPECTED_SOURCE_SHA256 and not args.allow_modified_source:
        raise RuntimeError("Source differs from the included verified revision.")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    nasm = tool(args.nasm)
    records = []

    def run(stem, argv):
        begin = time.perf_counter()
        stdout = output / (stem + ".stdout.txt")
        stderr = output / (stem + ".stderr.txt")
        with stdout.open("xb") as out, stderr.open("xb") as err:
            process = subprocess.run(argv, cwd=output, stdout=out, stderr=err, timeout=180)
        record = {"step": stem, "argv": list(map(str, argv)), "exit_code": process.returncode,
                  "duration_seconds": time.perf_counter() - begin,
                  "stdout": stdout.name, "stderr": stderr.name,
                  "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr)}
        records.append(record)
        if process.returncode:
            raise RuntimeError(f"{stem} failed with exit {process.returncode}; read {stderr}")

    outputs = []
    if args.target == "windows":
        linker = tool(args.windows_linker)
        obj = output / "pompetzki.obj"
        run("assemble", [nasm, "-f", "win64", str(source), "-o", str(obj)])
        for name, subsystem in (("pompetzki.exe", "console"), ("pompetzki-w.exe", "windows")):
            executable = output / name
            run("link-" + subsystem,
                [linker, "-nostdlib", "-o", str(executable), str(obj), "-lkernel32", "-lshell32",
                 "-Wl,-e,start", "-Wl,--subsystem," + subsystem, "-Wl,--no-insert-timestamp"])
            outputs.append(executable)
    else:
        linker = tool(args.linux_linker)
        obj = output / "pompetzki.o"
        executable = output / "pompetzki"
        run("assemble", [nasm, "-DLINUX", "-f", "elf64", str(source), "-o", str(obj)])
        run("link-linux", [linker, "-o", str(executable), str(obj), "-e", "_start"])
        outputs.append(executable)
    receipt = {"target": args.target, "source": source.name, "source_sha256": source_hash,
               "source_matches_verified_revision": source_hash == EXPECTED_SOURCE_SHA256,
               "steps": records, "outputs": [{"file": p.name, "sha256": sha(p), "bytes": p.stat().st_size} for p in outputs],
               "source_to_executable_correspondence": "Open"}
    with (output / "build-receipt.json").open("x", encoding="utf-8") as out:
        json.dump(receipt, out, indent=2)
    print(json.dumps(receipt, indent=2))

if __name__ == "__main__":
    main()
