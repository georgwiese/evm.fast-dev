#!/usr/bin/env python3
"""Offline feasibility arithmetic, not a Lean proof or an execution measurement.

Run from any directory; prints JSON. The triangle counts are hypothetical
worst-case probe allowances. No input realizing those collisions is asserted.
The parser deliberately accepts only the basic syntax used by this one loop.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "submission/InitECandidate/Proofs/BackendStages/Named188.lean"
text = SOURCE.read_text()
bodies = {
    int(index): body.strip()
    for index, body in re.findall(
        r"def NamedBody188_(\d+) : StackLang.HolProg 64 :=\n"
        r"(.*?)(?=\ndef |\ntheorem |\Z)", text, re.S
    )
}


def basic_stats(index):
    body = bodies[index]
    refs = [int(i) for i in re.findall(r"NamedBody188_(\d+)", body)]
    if body.startswith(".seq "):
        assert len(refs) == 2
        left, right = map(basic_stats, refs)
        return 1 + left[0] + right[0], left[1] + right[1]
    if body.startswith(".ite "):
        assert len(refs) == 2
        left, right = map(basic_stats, refs)
        return 1 + left[0] + right[0], max(left[1], right[1])
    assert not refs, (index, body)
    prefix = "Flapjack.Compiler.Backend.StackLang.Prog."
    assert body.startswith(prefix), (index, body)
    constructor = body[len(prefix):].split()[0]
    assert constructor in {"inst", "skip", "tick", "continue", "break"}, constructor
    return 1, int(constructor == "tick")


cap = 9007199254740984
startup = 23132
input_max = 134217712
nodes, ticks = basic_stats(192)
credits = nodes + ticks
assert (nodes, ticks, credits) == (35, 2, 37)
cases = []
for record_bytes in (4, 7, 36, 68):
    count = input_max // record_bytes
    probes = count * (count - 1) // 2
    cases.append({
        "hypothetical_bytes_per_record": record_bytes,
        "loose_record_count_ignoring_fixed_headers": count,
        "one_scan_triangular_occupied_probe_allowance": probes,
        "basic_credits_times_4_times_24_only": probes * credits * 4 * 24,
        "maximum_integer_target_cost_per_probe_using_all_remaining_budget":
            (cap - startup) // probes,
        "maximum_integer_work_credits_per_probe_ignoring_base_clock":
            (cap - startup) // (96 * probes),
    })

manifest = json.loads((ROOT / "work/agent-notes/proof-checks.json").read_text())
mismatches = []
for module in manifest["modules"]:
    path = ROOT / module["path"]
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != module["sha256"]:
        mismatches.append(module["path"])

print(json.dumps({
    "scope": "Source inspection and integer arithmetic; not kernel verification, "
             "not a whole-program bound, not a lower bound on actual runtime",
    "reviewed_proof_checkpoint": "04603be4d",
    "score_max": cap,
    "bootstrap_steps": startup,
    "input_visible_byte_bound_pending_formal_connection": input_max,
    "indexed_module_hashes_checked": len(manifest["modules"]),
    "indexed_module_hash_mismatches": mismatches,
    "probe_source": str(SOURCE.relative_to(ROOT)),
    "probe_source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    "probe_body": "NamedBody188_192",
    "basic_nodes": nodes,
    "basic_ticks": ticks,
    "basic_work_credits_per_body": credits,
    "target_price_for_these_extra_work_credits_only": credits * 4 * 24,
    "max_lab_clock_after_bootstrap": (cap - startup) // 24,
    "max_work_ignoring_base_clock_and_entry": (cap - startup) // 96,
    "old_uniform_source_multiplier": 24 * (4 * 12091 + 5) * 2 * 35 * 256,
    "system_regular_gas_in_six_calls": 6 * 30000000,
    "system_initial_reservoir_in_six_calls": 6 * 16 * 97920,
    "cases": cases,
    "caveats": [
        "Count bounds ignore fixed headers; large count and all-colliding distinct hashes "
        "are not proved simultaneously reachable.",
        "The four-byte record envelope allows empty duplicate preimages; it is not a "
        "distinct-key bound. Joint byte, distinctness and multiplicity constraints matter.",
        "The 36-byte row is a restricted scenario of 32-byte preimages plus offsets; "
        "it is not a bound on all witness records.",
        "htab_set also scans in htab_find_slot; the priced term omits that, empty-slot "
        "tests, hashing, setup, base clock and the rest of the guest.",
        "Failure of this upper-bound calculation does not establish any runtime lower "
        "bound, impossibility of finite K, or impossibility of a tighter proof.",
        "Source hash agreement rechecks integrity, not Lean proofs or the verifier.",
    ],
}, indent=2))
assert not mismatches, mismatches
