#!/usr/bin/env python3
"""Compile canonical-registry prefix proofs from fresh source copies."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


CORE_MODULES = (
    "Syn", "Prov", "Kal", "Val", "Inv", "Parse", "Data", "Checks", "Ax",
    "Sub", "Expand", "Replay", "ReplayT", "Replay2", "Replay3", "RpInit",
    "RpInitOk",
)
PROOF_MODULES = (
    "PrefixSoundness", "PrefixSoundnessReceipt", "CanonicalRegistryData",
    "CanonicalPrefixSoundness", "CanonicalPrefixSoundnessReceipt",
)
KERNEL_TARGETS = (
    "PMPRepair.PrefixSoundnessReceipt",
    "PMPRepair.CanonicalPrefixSoundnessReceipt",
)


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def locate_tool(name: str, fallback: str | None = None) -> str:
    found = shutil.which(name)
    if found is None and fallback is not None:
        found = shutil.which(fallback)
    if found is None:
        candidate = Path(name).expanduser()
        if candidate.is_file():
            found = str(candidate.resolve())
    if found is None:
        raise FileNotFoundError(f"Executable lookup failed: {name}")
    return str(Path(found).resolve())


def source_records(core: Path, proof: Path, manifest: dict) -> list[dict]:
    expected_core = {
        Path(item["path"]).name: item["sha256"]
        for item in manifest["required_core_sources"]
    }
    expected_proof = {
        Path(item["path"]).name: item["sha256"]
        for item in manifest["source_whitelist"] if item["role"] == "proof"
    }
    if set(expected_core) != {name + ".v" for name in CORE_MODULES}:
        raise ValueError("Manifest core module set differs from the builder module set")
    if set(expected_proof) != {name + ".v" for name in PROOF_MODULES}:
        raise ValueError("Manifest proof module set differs from the builder module set")
    records = []
    for group, directory, names, expected in (
        ("core", core, CORE_MODULES, expected_core),
        ("proof", proof, PROOF_MODULES, expected_proof),
    ):
        for name in names:
            source = directory / (name + ".v")
            actual = sha256(source)
            if actual != expected[source.name]:
                raise ValueError(f"Source SHA256 mismatch: {source}")
            records.append({
                "group": group,
                "module": name,
                "source": str(source),
                "sha256_before": actual,
                "manifest_sha256": expected[source.name],
            })
    return records


def record_command(label: str, argv: list[str], output: Path,
                   timeout: float) -> dict:
    stdout = output / "logs" / (label + ".stdout.txt")
    stderr = output / "logs" / (label + ".stderr.txt")
    start_utc = datetime.now(timezone.utc).isoformat()
    started = time.monotonic()
    timed_out = False
    error = None
    exit_code = None
    with stdout.open("wb") as out_stream, stderr.open("wb") as err_stream:
        try:
            process = subprocess.run(
                argv, cwd=output, stdout=out_stream, stderr=err_stream,
                timeout=timeout, check=False,
            )
            exit_code = process.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
        except OSError as exc:
            error = f"{type(exc).__name__}: {exc}"
            err_stream.write((error + "\n").encode("utf-8"))
    return {
        "label": label,
        "argv": argv,
        "working_directory": str(output),
        "start_utc": start_utc,
        "duration_seconds": round(time.monotonic() - started, 6),
        "exit_code": exit_code,
        "timeout": timed_out,
        "error": error,
        "stdout": str(stdout),
        "stderr": str(stderr),
    }


def successful(command: dict) -> bool:
    return command["exit_code"] == 0 and not command["timeout"] and command["error"] is None


def kernel_context(command: dict | None) -> dict:
    if command is None:
        return {"checked": False}
    text = (Path(command["stdout"]).read_text(encoding="utf-8", errors="replace")
            + Path(command["stderr"]).read_text(encoding="utf-8", errors="replace"))
    labels = {
        "axioms_none": "* Axioms: <none>",
        "type_in_type_none": "* Constants/Inductives relying on type-in-type: <none>",
        "unsafe_fixpoints_none": "* Constants/Inductives relying on unsafe (co)fixpoints: <none>",
        "assumed_positivity_none": "* Inductives whose positivity is assumed: <none>",
    }
    return {"checked": successful(command), **{
        key: value in text for key, value in labels.items()
    }}


def main() -> int:
    proof_source = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=Path, default=proof_source / ".." / ".." / "rocq",
                        help="directory containing the 17 released Cohen .v sources")
    parser.add_argument("--output", type=Path,
                        help="new build directory; defaults to a new temporary directory")
    parser.add_argument("--coqc", default="coqc", help="compiler executable or PATH name")
    parser.add_argument("--rocqchk", default="rocqchk",
                        help="kernel checker executable or PATH name; default also tries coqchk")
    parser.add_argument("--manifest", type=Path, default=proof_source / "public-source-inputs.json")
    parser.add_argument("--timeout", type=float, default=600,
                        help="maximum seconds for each native command (default: 600)")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")

    core_source = args.core.expanduser().resolve()
    manifest_path = args.manifest.expanduser().resolve()
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    inputs = source_records(core_source, proof_source, manifest)
    compiler = locate_tool(args.coqc)
    checker = locate_tool(args.rocqchk, "coqchk" if args.rocqchk == "rocqchk" else None)
    if args.output is None:
        output = Path(tempfile.mkdtemp(prefix="registry-proof-build-")).resolve()
    else:
        output = args.output.expanduser().resolve()
        if output == core_source or output == proof_source or output in core_source.parents or output in proof_source.parents:
            raise ValueError("Build output must be separate from source directories")
        output.mkdir(parents=True, exist_ok=False)
    (output / "core").mkdir()
    (output / "proof").mkdir()
    (output / "logs").mkdir()
    for item in inputs:
        destination = output / item["group"] / (item["module"] + ".v")
        shutil.copyfile(item["source"], destination)
        item["build_source"] = str(destination)
        if sha256(destination) != item["sha256_before"]:
            raise ValueError(f"Copied source SHA256 mismatch: {destination}")

    commands = []
    version = record_command("compiler-version", [compiler, "--version"], output, args.timeout)
    commands.append(version)
    search = ["-Q", str(output / "core"), "Cohen", "-Q", str(output / "proof"), "PMPRepair"]
    if successful(version):
        for item in inputs:
            command = record_command(
                item["group"] + "-" + item["module"] + "-compile",
                [compiler, *search, item["build_source"]], output, args.timeout,
            )
            commands.append(command)
            if not successful(command):
                break
    kernel = None
    if len(commands) == 23 and all(successful(command) for command in commands):
        kernel = record_command(
            "recursive-kernel-check", [checker, "-silent", "-o", *search, *KERNEL_TARGETS],
            output, args.timeout,
        )
        commands.append(kernel)

    assumption_counts = {}
    for name, expected_count in (("PrefixSoundnessReceipt", 6), ("CanonicalPrefixSoundnessReceipt", 7)):
        command = next((command for command in commands if command["label"] == "proof-" + name + "-compile"), None)
        count = 0
        if command is not None:
            text = Path(command["stdout"]).read_text(encoding="utf-8", errors="replace")
            count = len(re.findall(r"Closed under the global context", text))
        assumption_counts[name] = {"closed_count": count, "expected_count": expected_count}
    for item in inputs:
        item["sha256_after"] = sha256(Path(item["source"]))
        item["unchanged"] = item["sha256_before"] == item["sha256_after"]
    context = kernel_context(kernel)
    passed = (len(commands) == 24 and all(successful(command) for command in commands)
              and all(context.values()) and all(item["unchanged"] for item in inputs)
              and all(item["closed_count"] == item["expected_count"] for item in assumption_counts.values()))
    result = {
        "test": "Fresh source build and recursive canonical-registry proof check",
        "result": "passed" if passed else "failed",
        "candidate_release": manifest["candidate_release"],
        "public_source_commit": manifest["public_source_commit"],
        "source_manifest": str(manifest_path),
        "source_manifest_sha256": sha256(manifest_path),
        "output_directory": str(output),
        "fresh_core_modules": sum(command["label"].startswith("core-") and successful(command) for command in commands),
        "fresh_proof_modules": sum(command["label"].startswith("proof-") and successful(command) for command in commands),
        "commands": commands,
        "source_inputs": inputs,
        "kernel_context": context,
        "print_assumptions": assumption_counts,
        "scope": "Registry AST equality and conditional Gallina checker soundness. General executable/parser correspondence remains open.",
    }
    result_path = output / "build-result.json"
    result_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    hash_targets = [Path(__file__).resolve(), manifest_path]
    hash_targets.extend(path for path in output.rglob("*") if path.is_file())
    (output / "SHA256SUMS.txt").write_text(
        "".join(f"{sha256(path)}  {path}\n" for path in sorted(set(hash_targets))),
        encoding="utf-8",
    )
    print(json.dumps({
        "result": result["result"], "receipt": str(result_path),
        "hash_manifest": str(output / "SHA256SUMS.txt"),
        "fresh_core_modules": result["fresh_core_modules"],
        "fresh_proof_modules": result["fresh_proof_modules"],
        "kernel_seconds": kernel["duration_seconds"] if kernel else None,
        "kernel_context": context, "print_assumptions": assumption_counts,
    }, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as exc:
        print(f"{type(exc).__name__}: {exc}", file=sys.stderr)
        sys.exit(2)
