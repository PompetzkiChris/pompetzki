#!/usr/bin/env python3
"""Build the frozen canonical-registry pmp gate in a new output directory."""
import argparse
import datetime
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import time

SOURCE_SHA256 = "4d936cb8103c6aa97fb6ec290f88b3ee636c69f94f0cdb089a4621d9ba251d1b"
COMPILER_SHA256 = "660399e1aaa9f6954401b089d7656c74ca379090f35c89a022251915fc900e96"
BASE = pathlib.Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def linux_assembly(raw, runtime):
    marker = "; ---------------------------------------------------------------- runtime (pmpc)"
    if raw.count(marker) != 1:
        raise ValueError("Compiler assembly runtime marker must occur exactly once")
    code = raw.split(marker, 1)[0]
    code = re.sub(r"^extern .*\n", "", code, flags=re.M)
    startup = ("start:\n    and rsp, -16\n    sub rsp, 32\n"
               "    mov ecx, -11\n    call GetStdHandle\n    mov [hout], rax\n")
    replacement = ("start:\n    cmp qword [rsp], 2\n    jb .noarg\n"
                   "    mov rax, [rsp+16]\n    mov [argv1], rax\n"
                   "    and rsp, -16\n    jmp .begin\n.noarg:\n"
                   "    mov ecx, 2\n    call rt_exit\n.begin:\n")
    if startup not in code or code.count("section .bss\n") != 1:
        raise ValueError("Compiler assembly startup or storage marker differs")
    code = code.replace(startup, replacement)
    code = code.replace("section .bss\n", "section .bss\nargv1: resq 1\n", 1)
    return code + runtime + "\nsection .note.GNU-stack noalloc noexec nowrite progbits\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=pathlib.Path, required=True)
    parser.add_argument("--output", type=pathlib.Path, required=True,
                        help="New directory; existing directories are refused")
    parser.add_argument("--target", choices=["all", "windows", "linux"], default="all")
    parser.add_argument("--racket", default="racket", help="Racket executable or PATH name")
    parser.add_argument("--nasm", default="nasm", help="Windows-target assembler or PATH name")
    parser.add_argument("--windows-cc", default="gcc" if os.name == "nt" else "x86_64-w64-mingw32-gcc",
                        help="MinGW x64 GCC executable or PATH name")
    parser.add_argument("--linux-nasm", default="nasm", help="Linux assembler executable or PATH name")
    parser.add_argument("--linux-ld", default="ld", help="Linux linker executable or PATH name")
    parser.add_argument("--wsl-exe", help="Optional WSL executable or PATH name on Windows")
    parser.add_argument("--wsl-distro", help="Optional WSL distribution; omission uses its configured default")
    parser.add_argument("--timeout", type=int, default=180, help="Per-command timeout in seconds")
    args = parser.parse_args()
    source = args.source.resolve()
    dest = args.output.resolve()
    compiler = BASE / "pmpc-original.rkt"
    runtime_path = BASE / "linux-runtime.asm"
    if digest(source) != SOURCE_SHA256:
        raise ValueError("Source SHA256 differs from the frozen judge-v5.pmp gate")
    if digest(compiler) != COMPILER_SHA256:
        raise ValueError("Compiler SHA256 differs from the published compiler snapshot")
    want_windows = args.target in ("all", "windows")
    want_linux = args.target in ("all", "linux")
    if want_linux and os.name == "nt" and not args.wsl_exe:
        raise ValueError("Linux build on Windows requires an explicit --wsl-exe")
    if args.wsl_exe and os.name != "nt":
        raise ValueError("--wsl-exe is used only when running the builder on Windows")
    dest.mkdir(parents=True, exist_ok=False)
    rows = []

    def tool(name):
        found = shutil.which(name)
        if found is None:
            raise FileNotFoundError("Executable was not found: " + name)
        return found

    def run(name, command):
        so = dest / (name + ".stdout.txt")
        se = dest / (name + ".stderr.txt")
        began = time.perf_counter()
        with so.open("xb") as out, se.open("xb") as err:
            child = subprocess.run(command, cwd=dest, stdout=out, stderr=err, timeout=args.timeout)
        row = {"step": name, "command": command, "exit_code": child.returncode,
               "seconds": time.perf_counter() - began,
               "stdout": so.name, "stderr": se.name,
               "stdout_sha256": digest(so), "stderr_sha256": digest(se)}
        rows.append(row)
        with (dest / "build-progress.jsonl").open("a", encoding="utf-8") as progress:
            progress.write(json.dumps(row) + "\n")
        if child.returncode:
            raise RuntimeError("Build command failed: " + json.dumps(row))

    def wsl_prefix():
        prefix = [tool(args.wsl_exe)]
        if args.wsl_distro:
            prefix += ["-d", args.wsl_distro]
        return prefix + ["--exec"]

    def linux_path(path):
        if not args.wsl_exe:
            return str(path)
        child = subprocess.run(wsl_prefix() + ["wslpath", "-a", str(path)],
                               check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=args.timeout)
        return child.stdout.decode("utf-8").strip()

    def linux_command(executable, arguments):
        if args.wsl_exe:
            return wsl_prefix() + [executable] + arguments
        return [tool(executable)] + arguments

    windows_asm = dest / "judge-v5-base-windows.asm"
    run("lower-pmp", [tool(args.racket), str(compiler), str(source), str(windows_asm)])
    outputs = [windows_asm]
    if want_windows:
        obj = dest / "judge-v5-windows.obj"
        exe = dest / "judge-v5-windows.exe"
        run("assemble-windows", [tool(args.nasm), "-O0", "-f", "win64",
                                 str(windows_asm), "-o", str(obj)])
        run("link-windows", [tool(args.windows_cc), "-nostdlib", "-o", str(exe), str(obj),
                             "-lkernel32", "-Wl,-e,start", "-Wl,--image-base,0x400000",
                             "-Wl,--subsystem,console", "-Wl,--stack,67108864"])
        outputs.extend([obj, exe])
    if want_linux:
        asm = dest / "judge-v5-linux.asm"
        obj = dest / "judge-v5-linux.o"
        exe = dest / "judge-v5-linux"
        text = linux_assembly(windows_asm.read_text(encoding="utf-8"),
                              runtime_path.read_text(encoding="utf-8"))
        with asm.open("x", encoding="utf-8", newline="\n") as out:
            out.write(text)
        run("assemble-linux", linux_command(args.linux_nasm,
                                            ["-O0", "-f", "elf64", linux_path(asm), "-o", linux_path(obj)]))
        run("link-linux", linux_command(args.linux_ld,
                                        ["-o", linux_path(exe), linux_path(obj), "-e", "start"]))
        outputs.extend([asm, obj, exe])
    record = {"created_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "source": str(source), "source_sha256": digest(source),
              "compiler_sha256": digest(compiler), "linux_runtime_sha256": digest(runtime_path),
              "target": args.target, "steps": rows,
              "outputs": [{"file": p.name, "sha256": digest(p), "bytes": p.stat().st_size} for p in outputs],
              "source_native_correspondence": "Open; a build receipt is finite evidence only."}
    with (dest / "build-result.json").open("x", encoding="utf-8") as out:
        json.dump(record, out, indent=2)
    with (dest / "SHA256SUMS-build.txt").open("x", encoding="utf-8", newline="\n") as manifest:
        for path in sorted(dest.iterdir()):
            if path.is_file() and path.name != "SHA256SUMS-build.txt":
                manifest.write(digest(path) + " *" + path.name + "\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
