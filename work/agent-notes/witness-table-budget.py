#!/usr/bin/env python3
"""Offline joint witness-table feasibility calculation, never proof evidence.

Only reads fixed sources. No crypto assumption, Lean build, benchmark or network.
--self-test checks the relaxation against small exhaustive table executions and
an independent brute-force dimension search. See bound.md Section 3.R5.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BOOTSTRAP = 23132
BMAX = 134217712
STAGES = ROOT / "submission/InitECandidate/Proofs/BackendStages"
LINE_PREFIX = "Flapjack.Compiler.Backend.LabLang.Line."


def minimum_bytes(distinct, namespaces=1, alphabet=256):
    """Minimum aggregate length of distinct words in independent namespaces.

    Hash-distinct records have distinct representative preimages within each
    table. The same preimage can be represented once in each of two tables.
    This is a necessary size constraint; it says nothing about table buckets.
    """
    assert distinct >= 0 and namespaces > 0 and alphabet > 1
    total = 0
    available = namespaces
    tier_size = namespaces
    while distinct > available:
        total += distinct - available
        tier_size *= alphabet
        available += tier_size
    return total


def dimensions(n, d):
    assert 0 <= d <= n
    triangle = d * (d - 1) // 2
    return {
        "find_occupied": triangle + (n - d) * d,
        "raw_occupied": triangle,
        "empty_tests": 2 * d,
        "combined_occupied": d * (n - 1),
    }


def weighted(n, d, find_price, raw_price):
    p = dimensions(n, d)
    return find_price * p["find_occupied"] + raw_price * p["raw_occupied"]


def maximize(budget, find_price, raw_price, namespaces=1, alphabet=256):
    """Exact maximum of the stated integer dimension RELAXATION.

    4*N + minimum_bytes(D) <= budget; 1 <= D <= N.
    Split at preimage-length tiers and D mod 4. The objective is quadratic
    on each piece, so endpoints and the two nearest vertex integers suffice.
    For two tables this further relaxes away the absence of cross-table probes.
    """
    assert min(budget, find_price, raw_price) >= 0
    best = {"N": 0, "D": 0, "priced_occupied_only": 0,
            "minimum_preimage_bytes": 0, "relaxed_used_bytes": 0,
            **dimensions(0, 0)}
    lower, upper, length, correction = 1, namespaces, 0, 0
    tier_size = namespaces
    while 4 * lower + minimum_bytes(lower, namespaces, alphabet) <= budget:
        high = min(upper, (budget + correction) // (4 + length))
        for residue in range(4):
            tlo = (lower - residue + 3) // 4
            thi = (high - residue) // 4
            if tlo > thi:
                continue
            q = (budget + correction - length * residue) // 4

            def twice_cost(t):
                d = 4 * t + residue
                n = q - length * t
                # Polynomial extension, including t outside this piece.
                return (2 * find_price * n * d
                        + (raw_price - find_price) * d * d
                        - (find_price + raw_price) * d)

            f0, f1, f2 = map(twice_cost, (0, 1, 2))
            a = (f2 - 2 * f1 + f0) // 2
            b = f1 - f0 - a
            candidates = {tlo, thi}
            if a < 0:
                vertex = (-b) // (2 * a)
                candidates.update(range(vertex - 1, vertex + 3))
            for t in candidates:
                if not tlo <= t <= thi:
                    continue
                d = 4 * t + residue
                n = q - length * t
                assert 1 <= d <= n
                preimage_bytes = minimum_bytes(d, namespaces, alphabet)
                assert preimage_bytes == length * d - correction
                assert 4 * n + preimage_bytes <= budget
                cost = weighted(n, d, find_price, raw_price)
                assert 2 * cost == twice_cost(t)
                if cost > best["priced_occupied_only"]:
                    best = {"N": n, "D": d, "priced_occupied_only": cost,
                            "minimum_preimage_bytes": preimage_bytes,
                            "relaxed_used_bytes": 4 * n + preimage_bytes,
                            **dimensions(n, d)}
        correction += upper
        lower = upper + 1
        tier_size *= alphabet
        upper += tier_size
        length += 1
    return best


def padded_lines(section):
    source = (STAGES / f"Padded{section}.lean").read_text().split("\ntheorem")[0]
    lines = []
    for index, fragment in enumerate(source.split(LINE_PREFIX)[1:]):
        label = re.match(r"label (\d+) (\d+) 0", fragment)
        if label:
            assert int(label[1]) == section
            lines.append({"kind": "label", "label": int(label[2]),
                          "words": 0, "index": index})
            continue
        byte_lists = re.findall(r"\[(\d+#8(?:,\s*\d+#8)*)\]", fragment)
        assert len(byte_lists) == 1, (section, index)
        data = [int(x) for x in re.findall(r"(\d+)#8", byte_lists[0])]
        assert all(0 <= x < 256 for x in data) and len(data) % 4 == 0
        target = re.findall(r"Lab\.lab (\d+) (\d+)", fragment)
        assert len(target) <= 1
        if "AsmWithLab.jumpCmp " in fragment:
            kind = "branch"
        elif "AsmWithLab.jump " in fragment:
            kind = "jump"
        elif "HolAsm.jumpReg " in fragment:
            kind = "return"
        elif "AsmWithLab.halt" in fragment:
            kind = "halt"
        else:
            kind = "ordinary"
        lines.append({"kind": kind, "target": tuple(map(int, target[0])) if target else None,
                      "words": len(data) // 4, "index": index})
    return lines


def inspect_path(section, entry_label, branches, callee_words=None, callee_lines=None):
    """Count a stipulated literal path; does NOT prove it is executable.

    branches maps conditional LINE INDICES to the assumed taken Boolean.
    A call to memeq is counted and resumes at the known return label 185.4.
    All unrecognized transfers and missing branch choices are errors.
    """
    lines = padded_lines(section)
    labels = {line["label"]: i for i, line in enumerate(lines) if line["kind"] == "label"}
    start = labels[entry_label]
    pc, steps, words = start, 0, 0
    trace = []
    counts = Counter()
    for _ in range(500):
        line = lines[pc]
        if line["kind"] == "label":
            pc += 1
            continue
        trace.append(pc)
        counts[line["kind"]] += 1
        steps += 1
        words += line["words"]
        kind = line["kind"]
        if kind == "halt":
            raise AssertionError("unexpected failure path")
        if kind == "return":
            break
        if kind in {"jump", "branch"}:
            target_section, target_label = line["target"]
            taken = kind == "jump" or branches[pc]
            if taken:
                if (target_section, target_label) == (79, 0):
                    assert section == 185 and callee_words is not None
                    words += callee_words
                    steps += callee_lines
                    pc = labels[4]
                else:
                    assert target_section == section, (section, pc, line)
                    pc = labels[target_label]
                if pc == start:
                    break
                continue
        pc += 1
    else:
        raise AssertionError("stipulated path did not finish")
    return {"encoded_words": words, "nonlabel_lines_including_callee": steps,
            "caller_line_indices": trace, "caller_kinds": dict(counts),
            "assumed_branches_by_line_index": branches}


def loop_prices():
    source = (STAGES / "Named188.lean").read_text()
    bodies = {int(i): body.strip() for i, body in re.findall(
        r"def NamedBody188_(\d+) : StackLang.HolProg 64 :=\n"
        r"(.*?)(?=\ndef |\ntheorem |\Z)", source, re.S)}
    named_counts = Counter()

    def named_path(index):
        body = bodies[index]
        refs = [int(i) for i in re.findall(r"NamedBody188_(\d+)", body)]
        if body.startswith(".seq "):
            cost, stop = named_path(refs[0])
            if stop:
                return cost, True
            rest, stop = named_path(refs[1])
            return cost + rest, stop
        if body.startswith(".ite "):
            assert index == 183  # Assumed occupied-byte test is true.
            named_counts["ite"] += 1
            cost, stop = named_path(refs[0])
            return cost + 1, stop
        prefix = "Flapjack.Compiler.Backend.StackLang.Prog."
        assert body.startswith(prefix)
        kind = body[len(prefix):].split()[0]
        assert kind in {"inst", "skip", "tick", "continue"}
        named_counts[kind] += 1
        return (2 if kind == "tick" else 1), kind == "continue"

    named_credit, stops = named_path(192)
    assert named_credit == 15 and stops
    raw = inspect_path(188, 10, {90: False})
    comparisons = []
    for mismatch_word in range(5):
        choices = {6: True, 10: True, 61: False}
        for i in range(4):
            choices[(64, 70, 76, 82)[i]] = i != mismatch_word
        comparisons.append(inspect_path(79, 1, choices))
    longest = max(comparisons, key=lambda p: p["encoded_words"])
    find = inspect_path(185, 10, {73: False, 91: True, 137: True},
                        longest["encoded_words"], longest["nonlabel_lines_including_callee"])
    found = inspect_path(185, 10, {73: False, 91: True, 137: False},
                         comparisons[-1]["encoded_words"],
                         comparisons[-1]["nonlabel_lines_including_callee"])
    assert raw["encoded_words"] == 10
    assert [p["encoded_words"] for p in comparisons] == [17, 20, 23, 26, 26]
    assert find["encoded_words"] == 89
    assert found["encoded_words"] == 83
    return {"raw_occupied": raw, "find_occupied_mismatch": find,
            "find_occupied_match": found,
            "proposed_raw_named_path_work": named_credit,
            "raw_named_path_constructors": dict(named_counts),
            "memeq_aligned_32_first_mismatch_word_0_to_3_or_equal": comparisons,
            "status": "literal-path inspection, not a Lean execution or cost theorem; "
                      "target state relation, ABI, alignment, memory, failure and clock proofs missing"}


def self_test():
    sequences = [s for n in range(6) for s in product(range(3), repeat=n)]
    executions = 0
    queries = 0
    for homes in product(range(8), repeat=3):
        for sequence in sequences:
            slots = [None] * 8
            found_visits = raw_visits = 0
            for key in sequence:
                i = homes[key]
                while slots[i] is not None:
                    found_visits += 1
                    if slots[i] == key:
                        break
                    i = (i + 1) % 8
                if slots[i] == key:
                    continue
                j = homes[key]
                while slots[j] is not None:
                    raw_visits += 1
                    j = (j + 1) % 8
                assert j == i
                slots[j] = key
            d = len(set(sequence))
            bounds = dimensions(len(sequence), d)
            assert found_visits <= bounds["find_occupied"]
            assert raw_visits <= bounds["raw_occupied"]
            assert found_visits + raw_visits <= bounds["combined_occupied"]
            # Include absent keys and wraparound for every possible home slot.
            for query in range(4):
                starts = (homes[query],) if query < 3 else range(8)
                for home in starts:
                    i, occupied = home, 0
                    while slots[i] is not None:
                        occupied += 1
                        if slots[i] == query:
                            break
                        i = (i + 1) % 8
                    assert occupied <= d
                    queries += 1
            executions += 1
    optimizations = 0
    for namespaces, alphabet in product((1, 2), (2, 256)):
        # Independent sorted-list construction checks the layer-cake formula.
        word_lengths = [length for length in range(5)
                        for _ in range(namespaces * alphabet ** length)] if alphabet == 2 else (
                            [0] * namespaces + [1] * (namespaces * 256))
        for d in range(len(word_lengths) + 1):
            assert minimum_bytes(d, namespaces, alphabet) == sum(word_lengths[:d])
        for budget in range(101):
            for cf, cr in ((1, 1), (89, 10), (0, 3552), (10, 89)):
                brute = max([0] + [weighted(n, d, cf, cr)
                            for n in range(1, budget // 4 + 1)
                            for d in range(1, n + 1)
                            if 4 * n + minimum_bytes(d, namespaces, alphabet) <= budget])
                assert maximize(budget, cf, cr, namespaces, alphabet)["priced_occupied_only"] == brute
                optimizations += 1
    return {"table_executions": executions, "later_queries": queries,
            "brute_force_optimizer_comparisons": optimizations,
            "scope": "finite-model regression checks, not verification of guest semantics"}


def report():
    paths = loop_prices()
    cases = []
    prices = (("unit occupied visits", 1, 1),
              ("old raw basic work only", 0, 37 * 4 * 24),
              ("proposed raw path work only", 0, 15 * 4 * 24),
              ("proposed literal instruction prices", 89, 10))
    for namespaces in (1, 2):
        for label, cf, cr in prices:
            result = maximize(BMAX, cf, cr, namespaces)
            cases.append({"namespaces": namespaces, "price_status": label,
                          "find_price": cf, "raw_price": cr, **result})
    sources = [f"guest/src/{p}" for p in ("lib/htab.pnk", "lib/mem.pnk", "mpt.pnk", "ssz.pnk")]
    sources += [str((STAGES / f"{kind}{i}.lean").relative_to(ROOT))
                for kind in ("Named", "Padded") for i in (79, 185, 188, 190)]
    sources.append(str(Path(__file__).resolve().relative_to(ROOT)))
    manifest = json.loads((ROOT / "work/agent-notes/proof-checks.json").read_text())
    mismatches = [m["path"] for m in manifest["modules"]
                  if hashlib.sha256((ROOT / m["path"]).read_bytes()).hexdigest() != m["sha256"]]
    assert not mismatches, mismatches
    return {"status": "Conditional original-table upper bounds; no whole-program finite certificate",
            "objective": "Unchanged main implementation; no numerical ceiling",
            "scope": "exact arithmetic and fixed-literal path inspection; no kernel checking, "
                     "no formal evaluator run, and no reachable adversarial input asserted",
            "budget_bytes_pending_decoder_connection": BMAX,
            "bootstrap_steps": BOOTSTRAP,
            "generic_bounds": {
                "F": "D*(D-1)/2 + (N-D)*D", "R": "D*(D-1)/2",
                "F_with_multiplicities_in_first_insertion_order":
                    "D*(D-1)/2 + sum_{r=1}^D (m_r-1)*r",
                "F_plus_R": "D*(N-1)", "empty_tests": "2*D",
                "later_Q_queries_occupied": "Q*D", "later_empty_tests_at_most": "Q",
                "minimum_distinct_bytes_single_table_for_D_le_2pow32":
                    "(D-1)_+ + (D-257)_+ + (D-65793)_+ + (D-16843009)_+",
                "minimum_distinct_bytes_two_tables": "sum_k (D-2*sum_{j=0}^k 256^j)_+",
                "condition": "valid, non-full, non-growing, append-only linear-probing tables "
                             "with exact keys; no deletion or intervening mutation"},
            "paths": paths, "dimension_relaxations": cases,
            "unpriced_remainders": ["effective input/decoder and schema correspondence",
                "SSZ/hash work", "table initialization, allocation, growth-exclusion and key copies",
                "empty-slot tests, per-record setup and hashes", "later queries Q and trie traversal",
                "user and six system gas pools", "other tables, journals, refunds and cleanup",
                "output, failure/unwind and compiler entry/return/clock composition"],
            "indexed_proof_hashes_checked": len(manifest["modules"]),
            "indexed_proof_hash_mismatches": mismatches,
            "source_hashes": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources},
            "caveats": ["A maximum of this relaxation is an upper-bound calculation, not runtime evidence.",
                "Distinct preimages need not have distinct Keccak hashes or colliding table homes.",
                "Multiplicity and equality-prefix distributions can correlate with probe lengths.",
                "Two-table aggregate relaxation adds fictitious cross-table probes; it is conservative.",
                "Literal instruction counts need a new quantitative simulation theorem, including clocks.",
                "Literal target prices remain source inspection; checked original source-clock proofs do not establish those prices or a whole target bound."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.self_test:
        result["self_test"] = self_test()
    print(json.dumps(result, indent=2) + "\n", end="")


if __name__ == "__main__":
    main()
