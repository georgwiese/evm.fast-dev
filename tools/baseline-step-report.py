#!/usr/bin/env python3
"""Join an eest-run JSON with exact input bytes and gas fields, without network.

Gas limit follows Guest.GasLimit's total reader, including malformed inputs.
Payload gasUsed is an input claim, not independently measured execution gas.
The instruction counts remain Spike counts, never evaluateTargetHOL clocks.
"""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import statistics


def le(blob, offset, width):
    return int.from_bytes(blob[offset:offset + width], "little")


def input_fields(packed):
    if len(packed) < 8:
        raise ValueError("missing transport length")
    n = le(packed, 0, 8)
    end = 8 + n
    if len(packed) != end + (-end) % 8 or any(packed[end:]):
        raise ValueError("invalid transport length or padding")
    blob = packed[8:end]
    request = 2 + le(blob, 2, 4)
    payload = request + le(blob, request, 4)
    gas_limit = le(blob, payload + 412, 8)
    # A missing gasUsed field is unknown, not zero used gas.
    gas_used = le(blob, payload + 420, 8) if payload + 428 <= n else None
    return dict(input_bytes=n, input_sha256=hashlib.sha256(blob).hexdigest(),
                declared_gas_limit=gas_limit, payload_gas_used=gas_used,
                covered_gas=gas_limit <= 200_000_000)


def summary(rows):
    passing = [r for r in rows if r["class"].startswith("PASS") and
               r["spike_instructions"] is not None]
    counts = [r["spike_instructions"] for r in passing]
    ratios = [r for r in passing if r["payload_gas_used"] and r["covered_gas"]]
    highest = max(ratios, key=lambda r: r["spike_instructions"] / r["payload_gas_used"],
                  default=None)
    return dict(records=len(rows), counted_passing=len(counts),
                minimum=min(counts, default=None), maximum=max(counts, default=None),
                mean=statistics.mean(counts) if counts else None,
                covered_gas_records=sum(r["covered_gas"] for r in rows),
                highest_instructions_per_payload_gas=highest,
                units="Spike minstret delta; gasUsed is a payload claim")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("manifest", type=Path)
    ap.add_argument("results", type=Path)
    ap.add_argument("output", type=Path)
    args = ap.parse_args()
    manifest = {}
    with args.manifest.open() as f:
        for row in csv.reader(f, delimiter="\t"):
            if not row:
                continue
            if row[0] in manifest:
                raise ValueError(f"duplicate manifest label: {row[0]}")
            manifest[row[0]] = row
    records = json.loads(args.results.read_text())
    output = []
    seen = set()
    for record in records:
        label = record["label"]
        if label in seen:
            raise ValueError(f"duplicate result label: {label}")
        seen.add(label)
        row = manifest[label]
        path = Path(row[1])
        if not path.is_file():
            path = args.manifest.parent / path.name
        steps = record["steps"]
        if steps is not None and (type(steps) is not int or steps < 0):
            raise ValueError(f"invalid instruction count: {label}")
        output.append(dict(label=label, case_id=row[7] if len(row) > 7 else None,
                           classification_source="eest-run", **{"class": record["class"]},
                           spike_instructions=steps, **input_fields(path.read_bytes())))
    result = dict(summary=summary(output), records=output,
                  manifest_sha256=hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
                  results_sha256=hashlib.sha256(args.results.read_bytes()).hexdigest())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result["summary"], indent=2))


if __name__ == "__main__":
    main()
