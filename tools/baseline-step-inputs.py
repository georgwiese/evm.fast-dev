#!/usr/bin/env python3
"""Generate synthetic whole-guest inputs; no claim that they are valid blocks.

Malformed cases isolate copying before rejection. Structured SSZ cases exercise
decoding, payload hashing and witness ingestion before any later rejection.
Use the ordinary guest ELF, not a patched executable. A separate manifest.json
describes inputs without inventing expected roots or marking them as EEST passes.
"""
import argparse
import hashlib
import json
from pathlib import Path
import runpy
import struct


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("output", type=Path)
    ap.add_argument("--large", action="store_true", help="include 16 MiB and arena-limit inputs")
    ap.add_argument("--microbench", action="store_true",
                    help="generate inputs for work/agent-notes/microbench.pnk instead")
    args = ap.parse_args()
    helpers = runpy.run_path(str(Path(__file__).with_name("ssz-inputs.py")))
    args.output.mkdir(parents=True, exist_ok=True)
    rows = []

    if args.microbench:
        for mode, sizes, counts in [
                (0, [0], [0, 16, 64, 256, 1024, 4096]),
                (1, [64, 1024, 65536], [0, 1, 10]),
                (2, [32, 1024, 65536], [0, 1, 10]),
                (3, [32, 1024, 65536], [0, 1, 10])]:
            for size in sizes:
                for count in counts:
                    label = f"mode-{mode}-size-{size}-count-{count}"
                    name = label + ".bin"
                    (args.output / name).write_bytes(
                        helpers["pack"](struct.pack("<QQQ", mode, count, size)))
                    rows.append(dict(label=label, input_file=name, mode=mode,
                                     count=count, size=size))
        (args.output / "manifest.json").write_text(json.dumps(rows, indent=2) + "\n")
        print(f"generated {len(rows)} library diagnostic inputs")
        return

    def write(label, blob, purpose):
        path = args.output / (label + ".bin")
        packed = helpers["pack"](blob)
        # Spike prepends eight metadata bytes and writes the whole file. Keep
        # only the fixed host arena's visible bytes for oversized abstract blobs,
        # while retaining the original length word for input_blob's rejection.
        clipped = len(packed) > 134217720
        path.write_bytes(packed[:134217720])
        rows.append(dict(label=label, input_file=path.name, input_bytes=len(blob),
                         input_sha256=hashlib.sha256(blob).hexdigest(), purpose=purpose,
                         transport_clipped_to_arena=clipped))

    sizes = [0, 8, 1024, 65536, 1048576]
    if args.large:
        sizes += [16 * 1024**2, 134217712, 134217713]
    for n in sizes:
        write(f"invalid-schema-{n}", bytes(n), "copy then schema rejection; above arena limit traps")
    for n in [0, 1024, 65536, 1048576]:
        blob = helpers["stateless_input"](
            pl=helpers["payload"](gas_limit=0),
            wit=helpers["witness"](codes=[bytes(n)] if n else []))
        write(f"zero-gas-code-{n}", blob, "witness code ingestion at zero declared user gas")
    for count in [1, 16, 256, 4096]:
        blob = helpers["stateless_input"](
            pl=helpers["payload"](gas_limit=0, withdrawals=bytes(44 * count)))
        write(f"zero-gas-withdrawals-{count}", blob,
              "withdrawal decoding and hashing; execution may reject earlier")
    (args.output / "manifest.json").write_text(json.dumps(rows, indent=2) + "\n")
    print(f"generated {len(rows)} synthetic inputs")


if __name__ == "__main__":
    main()
