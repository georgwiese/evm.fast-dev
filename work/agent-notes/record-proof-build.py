#!/usr/bin/env python3
"""Index printed axiom checks from successful local builds of unchanged sources.

This is local evidence bookkeeping, not the submission verifier. Supply a
Solver subdirectory and one or more completed successful build logs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('subdirectory')
parser.add_argument('logs', nargs='+')
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
notes = root / 'work/agent-notes'
facts = {}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for log_name in args.logs:
    path = notes / 'logs' / log_name
    log = path.read_text()
    assert 'Build completed successfully' in log, path
    assert not re.search(r'^error:', log, re.M), path
    for name, axiom_text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log):
        if not name.startswith('InitECandidate.Solver.'):
            continue
        axioms = [a.strip() for a in axiom_text.split(',') if a.strip()]
        assert set(axioms) <= allowed, (name, axioms)
        facts[name] = {'theorem': name, 'axioms': axioms, 'successful_log': path.name}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        if name.startswith('InitECandidate.Solver.'):
            facts[name] = {'theorem': name, 'axioms': [], 'successful_log': path.name}
record_path = notes / 'proof-checks.json'
record = json.loads(record_path.read_text())
modules = {entry['path']: entry for entry in record['modules']}
theorems = {entry['theorem']: entry for entry in record['theorems']}
added = 0
for source in sorted((root / 'submission/InitECandidate/Solver' / args.subdirectory).rglob('*.lean')):
    rel = str(source.relative_to(root))
    names = re.findall(r'^#print axioms ([\w.]+)$', source.read_text(), re.M)
    if not names or not all(name in facts for name in names):
        continue
    added += rel not in modules
    modules[rel] = {'path': rel, 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
    for name in names:
        theorems[name] = facts[name]
record['modules'] = sorted(modules.values(), key=lambda entry: entry['path'])
record['theorems'] = list(theorems.values())
record_path.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'added_modules': added, 'checked_modules': len(modules), 'main_theorems': len(theorems)}))
