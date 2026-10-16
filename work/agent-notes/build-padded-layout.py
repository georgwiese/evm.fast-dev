#!/usr/bin/env python3
"""Build fixed-section facts in chunks under one inherited Lean limiter.

Run inside tools/limited-lake.py and baseline-resource-run.py. Sequential chunk
requests avoid launching thousands of waiting Lean processes at once; each Lake
request still uses all available limiter slots. A failed chunk stops the run.
"""
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
CHUNKS = ROOT / "submission/InitECandidate/Solver/LabBound/Padded"
paths = sorted(CHUNKS.glob("Chunk*.lean"), key=lambda p: int(p.stem[5:]))
assert [p.stem for p in paths] == [f"Chunk{i}" for i in range(54)]
modules = ["InitECandidate.Solver.LabBound.StaticTarget"]
modules += [f"InitECandidate.Solver.LabBound.Padded.{p.stem}" for p in paths]
modules.append("InitECandidate.Solver.LabBound.PaddedProgram")
modules.append("InitECandidate.Solver.LabBound.PaddedRiscV")
for i, module in enumerate(modules):
    start = time.monotonic()
    print(f"BEGIN {i + 1}/{len(modules)} {module}", flush=True)
    subprocess.run(["lake", "build", module], cwd=ROOT, check=True)
    print(f"END {i + 1}/{len(modules)} {module} {time.monotonic() - start:.2f}s", flush=True)
