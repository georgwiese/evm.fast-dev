#!/usr/bin/env python3
"""Text-only constructor inventory of fixed Stack procedure literals.

This is planning evidence, not a Lean proof of the complete installed program.
It excludes the small runtime/bootstrap procedures outside these numbered files.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[2]
base = root / 'submission/InitECandidate/Proofs/BackendStages'
report = {'kind': 'text_scan_not_kernel_proof', 'stages': {}}
for stage in ['Raw', 'Alloc', 'Removed']:
    files = sorted(p for p in base.glob(stage + '*.lean')
                   if re.fullmatch(stage + r'\d+\.lean', p.name))
    totals = {c: 0 for c in ['storeConsts', 'install', 'alloc', 'stackAlloc']}
    records = []
    for path in files:
        data = path.read_bytes()
        source = data.decode()
        counts = {c: len(re.findall(r'\.' + c + r'\b', source)) for c in totals}
        for c in totals:
            totals[c] += counts[c]
        records.append({'path': str(path.relative_to(root)),
                        'sha256': hashlib.sha256(data).hexdigest(), 'counts': counts})
    report['stages'][stage] = {'file_count': len(files), 'totals': totals, 'files': records}
(root / 'work/agent-notes/stack-constructor-scan.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({stage: {'file_count': record['file_count'], 'totals': record['totals']}
                  for stage, record in report['stages'].items()}))
