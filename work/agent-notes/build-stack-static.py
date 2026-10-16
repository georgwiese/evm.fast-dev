#!/usr/bin/env python3
"""Build fixed Raw/Alloc syntax checks under the inherited shared Lean limiter.

Run inside tools/limited-lake.py and baseline-resource-run.py. Sequential
chunks limit the number of waiting processes; a failure stops the driver.
"""
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
CHUNKS = ROOT / "submission/InitECandidate/Solver/StackStatic"
paths = sorted(CHUNKS.glob("Chunk*.lean"), key=lambda p: int(p.stem[5:]))
assert [p.stem for p in paths] == [f"Chunk{i}" for i in range(52)]
modules = [f"InitECandidate.Solver.StackStatic.{p.stem}" for p in paths]
modules.append("InitECandidate.Solver.StackStatic.Programs")
for i, module in enumerate(modules):
    start = time.monotonic()
    print(f"BEGIN {i + 1}/{len(modules)} {module}", flush=True)
    subprocess.run(["lake", "build", module], cwd=ROOT, check=True)
    print(f"END {i + 1}/{len(modules)} {module} {time.monotonic() - start:.2f}s", flush=True)
