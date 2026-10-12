"""Extract every RECORDCOUNT call from the pinned judge-v6.pmp.

Source text only. This does not run the interpreter, the kernel, or a suite.
"""
import hashlib
import json
from pathlib import Path

SOURCE = Path("/tmp/a131/src/Abschluss-1.3.1-source/judge/judge-v6.pmp")
PIN = "87562735cf20dfd18eb5f26348878b2ac6306bc78714d6953565df9c833d0dc7"
OUT = Path("/tmp/pompetzki-pub/audit/grok-gate/release-1.3.1-recordcount-callers")

data = SOURCE.read_bytes()
digest = hashlib.sha256(data).hexdigest()
if digest != PIN or len(data) != 101261:
    raise SystemExit(f"pinned judge mismatch {len(data)} {digest}")
lines = data.decode("utf-8").splitlines()

def is_comment(line):
    return line.lstrip().startswith(";")

def numbered(start, end):
    return [{"line": n, "text": lines[n - 1]} for n in range(start, end + 1)]

def executed_heap_switch(start, end):
    hits = []
    for n in range(start, end + 1):
        text = lines[n - 1].strip()
        if text in {"gosub ALLOC", "gosub TOSCR0", "gosub TOSCR1", "gosub TOPERS"} or text.startswith("set curp "):
            hits.append({"line": n, "text": lines[n - 1]})
    return hits

calls = [i for i, line in enumerate(lines, 1) if line.strip() == "gosub RECORDCOUNT"]
rdlist_calls = [i for i, line in enumerate(lines, 1) if line.strip() == "gosub RDLIST"]
if calls != [153, 200, 591]:
    raise SystemExit(f"unexpected RECORDCOUNT calls: {calls}")
if rdlist_calls != [131, 195, 228, 663, 2021, 2062, 2136]:
    raise SystemExit(f"unexpected RDLIST calls: {rdlist_calls}")

code_lines = [(i, line) for i, line in enumerate(lines, 1) if not is_comment(line)]
writes = [
    {"line": i, "text": line}
    for i, line in code_lines
    if line.startswith(("set pos ", "set lim ", "set curp ", "set num "))
]
noncomment_text = "\n".join(line for _, line in code_lines)
comment_text = "\n".join(line for line in lines if is_comment(line))

def previous_rdnum(call):
    for i in range(call - 1, 0, -1):
        if lines[i - 1].strip() == "gosub RDNUM":
            return i
    return None

def next_alloc(call):
    for i in range(call + 1, len(lines) + 1):
        if lines[i - 1].strip() == "gosub ALLOC":
            return i
    return None

heap_paths = {
    153: {
        "block": "persistent PB",
        "evidence": executed_heap_switch(65, 152),
        "note": "No TOSCR0, TOSCR1, or TOPERS in lines 65-152. ALLOC at 71 and 120 advances curp inside the persistent block.",
    },
    200: {
        "block": "scratch SB",
        "evidence": executed_heap_switch(190, 199),
        "note": "Line 194 is gosub TOSCR0. Its body, lines 381-385, sets curp to SB before this call.",
    },
    591: {
        "block": "the block of the RDLIST caller",
        "evidence": executed_heap_switch(587, 590),
        "note": "RDLIST itself does not switch curp before RECORDCOUNT. The caller does.",
    },
}
if any(row["text"].strip() in {"gosub TOSCR0", "gosub TOSCR1", "gosub TOPERS"} for row in heap_paths[153]["evidence"]):
    raise SystemExit("theorem-count span unexpectedly switches blocks")
if not any(row["text"].strip() == "gosub TOSCR0" for row in heap_paths[200]["evidence"]):
    raise SystemExit("step-count span is missing TOSCR0")

sites = []
for call in calls:
    rd = previous_rdnum(call)
    alloc = next_alloc(call)
    between = numbered(rd, call)
    num_assignments = [row for row in between[1:-1] if row["text"].startswith("set num ")]
    sites.append({
        "gosub_RECORDCOUNT_line": call,
        "preceding_gosub_RDNUM_line": rd,
        "lines_from_rdnum_through_call": between,
        "num_assigned_between_rdnum_and_call": num_assignments,
        "next_gosub_ALLOC_line": alloc,
        "lines_from_call_through_alloc": numbered(call, alloc),
        "executed_heap_path": heap_paths[call],
    })

caller_heap = {
    131: "persistent PB; lines 65-130 contain ALLOC but no TOSCR0 or TOPERS",
    195: "scratch SB; line 194 is gosub TOSCR0 immediately before this RDLIST",
    228: "persistent pointer saved by TOSCR0; line 227 is gosub TOPERS immediately before this RDLIST",
    663: "the block of whoever called PARSEF; PF_P does not switch curp",
    2021: "scratch SB; ST_USE is reached from gosub STEP at line 217, after TOSCR0 at 194 and before TOPERS at 227",
    2062: "scratch SB; ST_SPEC is reached from the same STEP interval",
    2136: "scratch SB; ST_TAUT is reached from the same STEP interval",
}
rdlist_sites = []
for call in rdlist_calls:
    rdlist_sites.append({
        "gosub_RDLIST_line": call,
        "window": numbered(max(1, call - 3), call),
        "caller_heap": caller_heap[call],
        "heap_switches_in_preceding_four_lines": executed_heap_switch(max(1, call - 4), call - 1),
    })

report = {
    "source": "Abschluss-1.3.1-source/judge/judge-v6.pmp",
    "local_path": str(SOURCE),
    "bytes": len(data),
    "sha256": digest,
    "source_analysis_only": True,
    "kernel_proof": False,
    "native_compiler_os_permissions": False,
    "gosub_RECORDCOUNT_lines": calls,
    "gosub_RDLIST_lines": rdlist_calls,
    "recordcount_definition_lines": numbered(396, 405),
    "sites": sites,
    "rdlist_callers": rdlist_sites,
    "position_limit_heap_num_writes": writes,
    "comment_mentions_999999999999": "999999999999" in comment_text,
    "instruction_mentions_999999999999": "999999999999" in noncomment_text,
    "instruction_mentions_2_pow_62": "4611686018427387904" in noncomment_text or "2^62" in noncomment_text,
    "instruction_compares_lim_and_curp": any("lim" in line and "curp" in line for _, line in code_lines),
    "invariants": {
        "num_upper_bound": "Each call is immediately after RDNUM. RDNUM's comment names 0..999999999999, but no instruction compares num with 999999999999. The source gate is the significant-digit test at lines 555-558, which refuses a 13th significant digit before mul or add. Nothing assigns num between that RDNUM and the call. The integer inequality is not a source comparison and is not a kernel proof.",
        "num_lower_bound": "RDNUM sets num to 0 and returns only after nseen is 1. A returned value is built from digits. Nonnegativity is the shape of that routine, not a comparison with zero and not a kernel proof.",
        "pos_le_lim": "No instruction tests pos <= lim at a RECORDCOUNT call. SKIPWS, RDNUM, and RDTAG advance pos by 1 only after pos < lim. The header adds 4 only after lim - pos >= 4. Those are scanning patterns. They establish pos <= lim only if the initial J0_len is nonnegative, and the source never tests J0_len.",
        "zero_le_pos": "No instruction compares pos with 0. pos is set from the read buffer J0 and from text-buffer addresses. Nonnegativity is unproved.",
        "lim_le_hp": "The source heap pointer is curp. No instruction compares lim with curp. lim <= hp is unproved.",
        "hp_lt_2_pow_62": "Neither 4611686018427387904 nor 2^62 occurs in an instruction. The block sizes are constants 201326592, 402653184, and 16777216. They do not bound the address returned by alloc or the input pointer. hp < 2^62 is unproved.",
        "subsequent_allocation": "ALLOC checks curp + an against the current block end and stops at LIMITMEM. That is a block-capacity check. It is not the address contract. The theorem call then allocates (nreg + nthm) * 24. The step call allocates max(nsteps * 8, 8). RDLIST allocates ln * 8.",
    },
}
(OUT / "call-map.json").write_text(json.dumps(report, indent=2) + "\n")
raw = OUT / "raw"
raw.mkdir(exist_ok=True)
for site in sites:
    body = site["lines_from_rdnum_through_call"] + site["lines_from_call_through_alloc"][1:]
    (raw / f"call-{site['gosub_RECORDCOUNT_line']}.txt").write_text(
        "".join(f"{row['line']}:{row['text']}\n" for row in body)
    )
(raw / "recordcount-definition.txt").write_text(
    "".join(f"{row['line']}:{row['text']}\n" for row in report["recordcount_definition_lines"])
)
(raw / "rdnum.txt").write_text("".join(f"{n}:{lines[n - 1]}\n" for n in range(529, 573)))
(raw / "input-heap-alloc.txt").write_text(
    "".join(f"{n}:{lines[n - 1]}\n" for n in list(range(47, 77)) + list(range(372, 406)))
)
(raw / "theorem-count-context.txt").write_text("".join(f"{n}:{lines[n - 1]}\n" for n in range(144, 157)))
(raw / "step-count-context.txt").write_text("".join(f"{n}:{lines[n - 1]}\n" for n in range(188, 209)))
(raw / "rdlist-callers.txt").write_text("".join(
    f"{row['line']}:{row['text']}\n" for site in rdlist_sites for row in site["window"]
))
print(json.dumps({
    "sha256": digest,
    "calls": calls,
    "rdlist": rdlist_calls,
    "instruction_mentions_999999999999": report["instruction_mentions_999999999999"],
    "instruction_mentions_2_pow_62": report["instruction_mentions_2_pow_62"],
    "between": [
        {
            "call": site["gosub_RECORDCOUNT_line"],
            "rdnum": site["preceding_gosub_RDNUM_line"],
            "alloc": site["next_gosub_ALLOC_line"],
            "num_assignments_between": site["num_assigned_between_rdnum_and_call"],
            "heap": site["executed_heap_path"]["block"],
        }
        for site in sites
    ],
}, indent=2))
