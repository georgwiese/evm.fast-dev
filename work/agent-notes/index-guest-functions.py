#!/usr/bin/env python3
"""Index fixed Crep output names and corresponding Named Stack labels for navigation.

This is a source-navigation aid, not a proof of compiler correctness or costs.
The actual literal modules and their existing equalities remain authoritative.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
rows = []
for number in range(826):
    crep = ROOT / f'submission/InitECandidate/Proofs/FrontendStages/Crep/Data{number}.lean'
    with crep.open('rb') as stream:
        stream.seek(max(0, crep.stat().st_size - 4096))
        tail = stream.read().decode()
    match = re.search(r'def output\d+.*?implode\s*\[([^]]*)\]', tail, re.S)
    assert match, crep
    name = bytes(map(int, re.findall(r'(\d+)#8', match[1]))).decode('ascii')
    label = number + 64
    stack = ROOT / f'submission/InitECandidate/Proofs/BackendStages/Named{label}.lean'
    text = stack.read_text()
    assert re.search(rf'def Named{label} : .*?:=\s*\({label},', text), stack
    rows.append({'name': name, 'crep_procedure': number, 'stack_label': label,
                 'crep_path': str(crep.relative_to(ROOT)), 'stack_path': str(stack.relative_to(ROOT)),
                 'crep_sha256': hashlib.sha256(crep.read_bytes()).hexdigest(),
                 'stack_sha256': hashlib.sha256(stack.read_bytes()).hexdigest()})
assert len({row['name'] for row in rows}) == len(rows)
out = ROOT / 'work/agent-notes/guest-function-index.json'
out.write_text(json.dumps({'description': __doc__, 'functions': rows}, indent=2) + '\n')
print(json.dumps({'indexed': len(rows), 'output': str(out)}))
for row in rows:
    if row['name'] in {'charge_gas', 'extend_memory', 'frame_mem_alloc', 'memory_gas_cost', 'charge_with_memory'}:
        print(row['name'], row['crep_procedure'], row['stack_label'])
