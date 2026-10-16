#!/usr/bin/env python3
"""Planning scan of named Word syntax DAGs; every bound still needs Lean decide.

Data64 and Data713 use different literal formats and are covered by existing
kernel checks, not this parser. Reject unfamiliar constructor/reference shapes.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
leafs = {'move', 'tick', 'inst', 'get', 'ffi', 'return', 'opCurrHeap', 'set',
         'continue', 'break', 'skip', 'shareInst', 'raise'}
records = []
for ident in range(64, 890):
    if ident in (64, 713):
        continue
    path = ROOT / f'submission/InitECandidate/Proofs/StackAnalysis/Data{ident}.lean'
    source = path.read_text()
    defs = re.finditer(r'^def (optimizedBody\d+_\d+) : WordLangProgHOL \(BitVec 64\) :=\n(.*?)(?=^def |^end )', source, re.M | re.S)
    facts = {}
    for d in defs:
        name, body = d[1], d[2].strip()
        m = re.match(r'(?:Flapjack.WordLangProgHOL|)\.([a-zA-Z]+)\b', body)
        assert m, (ident, name, body[:100])
        kind = m[1]
        refs = re.findall(r'optimizedBody\d+_\d+', body)
        assert all(r in facts for r in refs), (ident, name, refs)
        # Composite syntax is named, rather than nested inline, in these files.
        assert not re.search(r'(?:Flapjack.WordLangProgHOL|)\.(?:seq|ite|loop|mustTerminate|call|shareInst|raise)\b', body[m.end():]), (ident, name, 'inline composite')
        costs = [facts[r][0] for r in refs]
        ceilings = [facts[r][1] for r in refs]
        if kind == 'seq':
            assert len(refs) == 2
            cost = sum(costs)
        elif kind == 'ite':
            assert len(refs) == 2
            cost = max(costs)
        elif kind in ('loop', 'mustTerminate'):
            assert len(refs) == 1
            cost = costs[0]
        elif kind == 'call':
            assert len(refs) <= 2
            cost = 0
        else:
            assert kind in leafs and not refs, (ident, name, kind, refs)
            cost = int(kind in ('shareInst', 'raise'))
        facts[name] = (cost, max([cost] + ceilings))
    root = re.search(r'^def optimized\d+ : Nat × Nat × WordLangProgHOL \(BitVec 64\) :=\n\(\d+, \d+, (optimizedBody\d+_\d+)\)', source, re.M)
    assert root and root[1] in facts, ident
    cost, ceiling = facts[root[1]]
    records.append({'procedure': ident, 'cost': cost, 'ceiling': ceiling,
                    'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
result = {'description': 'Untrusted planning DAG scan; kernel bounds must be built separately.',
          'excluded_formats': [64, 713], 'procedures': records,
          'maximum_scanned_ceiling': max(r['ceiling'] for r in records)}
(ROOT / 'work/agent-notes/word-ceiling-dag.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'scanned': len(records), 'maximum': result['maximum_scanned_ceiling'],
                  'over4': [r for r in records if r['ceiling'] > 4]}))
