#!/usr/bin/env python3
"""Text-only constructor inventory of fixed Stack procedure literals.

This is planning evidence, not a Lean proof of the complete installed program.
It includes each stage's runtime stubs; it is not an assembled-code equality proof.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[2]
base = root / 'submission/InitECandidate/Proofs/BackendStages'
reference_patterns = {
    'indirect_sum_target': r'Sum\.inr\b',
    'direct_label_6': r'Sum\.inl\s+6\b',
    'raw_call_6': r'\.rawCall\s+6\b',
    'jump_lower_6': r'\.jumpLower\s+\d+\s+\d+\s+6\b',
    'location_6': r'\.locValue\s+\d+\s+6\b',
}
report = {'kind': 'text_scan_not_kernel_proof', 'stages': {}}
for stage in ['Raw', 'Alloc', 'Removed']:
    files = sorted(p for p in base.glob(stage + '*.lean')
                   if re.fullmatch(stage + r'(?:\d+|Stubs)\.lean', p.name))
    totals = {c: 0 for c in ['storeConsts', 'install', 'alloc', 'stackAlloc']}
    references = {name: 0 for name in reference_patterns}
    records = []
    for path in files:
        data = path.read_bytes()
        source = data.decode()
        counts = {c: len(re.findall(r'\.' + c + r'\b', source)) for c in totals}
        for name, pattern in reference_patterns.items():
            references[name] += len(re.findall(pattern, source))
        for c in totals:
            totals[c] += counts[c]
        records.append({'path': str(path.relative_to(root)),
                        'sha256': hashlib.sha256(data).hexdigest(), 'counts': counts})
    report['stages'][stage] = {'file_count': len(files), 'totals': totals, 'text_reference_counts': references, 'files': records}
(root / 'work/agent-notes/stack-constructor-scan.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({stage: {'file_count': record['file_count'], 'totals': record['totals'], 'text_reference_counts': record['text_reference_counts']}
                  for stage, record in report['stages'].items()}))
