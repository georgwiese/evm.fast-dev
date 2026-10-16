#!/usr/bin/env python3
"""Untrusted planning scan of fixed Crep DAGs; Lean must check every bound.

Count comparison nodes in literal expressions and propagate the exact local
cost/ceiling recurrence over named program nodes. Reject unfamiliar syntax.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'submission/InitECandidate/Proofs/FrontendStages/Crep'
records = []
leafs = {'skip', 'break', 'continue', 'tick', 'raise', 'primitive', 'extCall',
         'return', 'assign', 'store', 'store32', 'storeByte', 'storeGlob', 'shMem'}
for ident in range(826):
    path = DATA / f'Data{ident}.lean'
    source = path.read_text()
    nodes = re.finditer(r'^def (crepBody\d+_\d+) : CrepProg \(BitVec 64\) :=\n(.*?)(?=^def |^end )', source, re.M | re.S)
    facts = {}
    for node in nodes:
        name, body = node[1], node[2].strip()
        head = re.match(r'(?:Flapjack.CrepProg|)\.([a-zA-Z]+)\b', body)
        assert head, (ident, name, body[:80])
        kind = head[1]
        refs = re.findall(r'crepBody\d+_\d+', body)
        assert all(r in facts for r in refs), (ident, name, refs)
        assert not re.search(r'(?:Flapjack.CrepProg|)\.(?:dec|seq|ite|while|call)\b', body[head.end():]), (ident, name, 'inline composite')
        # Expression nodes are inline literals, not shared named DAGs.
        assert not re.search(r'\b(?:crepExp|crepExpr|expression)\w*', body), (ident, name, 'expression reference')
        comparisons = len(re.findall(r'\bFlapjack.CrepExp\.cmp\b', body))
        assert len(re.findall(r'\.cmp\b', body)) == comparisons, (ident, name, 'unqualified comparison')
        costs = [facts[r][0] for r in refs]
        ceilings = [facts[r][1] for r in refs]
        if kind == 'dec':
            assert len(refs) == 1
            cost = comparisons + costs[0]
        elif kind == 'seq':
            assert len(refs) == 2 and comparisons == 0
            cost = sum(costs)
        elif kind == 'ite':
            assert len(refs) == 2
            cost = comparisons + max(costs) + 1
        elif kind == 'while':
            assert len(refs) == 1
            cost = comparisons + 2
        elif kind == 'call':
            assert len(refs) <= 1
            cost = comparisons
        else:
            assert kind in leafs and not refs, (ident, name, kind, refs)
            cost = comparisons
        facts[name] = (cost, max([cost] + ceilings))
    root = re.search(r'^def data\d+ : CrepProg \(BitVec 64\) := (crepBody\d+_\d+)$', source, re.M)
    assert root and root[1] in facts, ident
    cost, ceiling = facts[root[1]]
    records.append({'procedure': ident, 'cost': cost, 'ceiling': ceiling,
                    'nodes': len(facts), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
result = {'description': 'Untrusted planning DAG scan; kernel bounds must be built separately.',
          'procedures': records, 'maximum_scanned_ceiling': max(r['ceiling'] for r in records)}
(ROOT / 'work/agent-notes/crep-ceiling-dag.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'scanned': len(records), 'maximum': result['maximum_scanned_ceiling'],
                  'largest': sorted(records, key=lambda r:r['ceiling'], reverse=True)[:10]}))
