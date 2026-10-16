#!/usr/bin/env python3
"""Build fixed Crep checks in bounded chunks under the shared Lean limiter.

Invoke within baseline-resource-run.py and limited-lake.py. This is a targeted
static-code proof build, never the full baseline verifier or audit.
"""
from pathlib import Path
import argparse
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
ap = argparse.ArgumentParser()
ap.add_argument('--start-chunk', type=int, default=0)
ap.add_argument('--end-chunk', type=int, default=51)
args = ap.parse_args()
assert 0 <= args.start_chunk <= args.end_chunk <= 51
NS = 'InitECandidate.Solver.CrepStatic'
modules = [f'{NS}.Chunk{i}' for i in range(args.start_chunk,args.end_chunk+1)]
if args.end_chunk == 51:
    modules += [f'{NS}.Programs',f'{NS}.Fixed']
for i,module in enumerate(modules):
    start = time.monotonic()
    print(f'BEGIN {i+1}/{len(modules)} {module}',flush=True)
    subprocess.run(['lake','build',module],cwd=ROOT,check=True)
    print(f'END {i+1}/{len(modules)} {module} {time.monotonic()-start:.2f}s',flush=True)
