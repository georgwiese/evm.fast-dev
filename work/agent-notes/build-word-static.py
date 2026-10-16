#!/usr/bin/env python3
"""Build fixed Word cost/no-Install checks under the inherited shared Lean limiter.

Run inside tools/limited-lake.py and baseline-resource-run.py. Sequential
chunks limit the number of waiting processes; a failure stops the driver.
"""
from pathlib import Path
import subprocess
import time
import argparse

ROOT = Path(__file__).resolve().parents[2]
CHUNKS = ROOT / "submission/InitECandidate/Solver/WordStatic"
paths = sorted(CHUNKS.glob("Chunk*.lean"), key=lambda p: int(p.stem[5:]))
assert [p.stem for p in paths] == [f"Chunk{i}" for i in range(52)]
modules = [f"InitECandidate.Solver.WordStatic.{p.stem}" for p in paths]
modules.append("InitECandidate.Solver.WordStatic.Programs")
modules.append("InitECandidate.Solver.WordStatic.Fixed")
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--start-chunk', type=int, default=0)
args = parser.parse_args()
assert 0 <= args.start_chunk < 52
for i, module in enumerate(modules[args.start_chunk:], start=args.start_chunk):
    start = time.monotonic()
    print(f"BEGIN {i + 1}/{len(modules)} {module}", flush=True)
    subprocess.run(["lake", "build", module], cwd=ROOT, check=True)
    print(f"END {i + 1}/{len(modules)} {module} {time.monotonic() - start:.2f}s", flush=True)
