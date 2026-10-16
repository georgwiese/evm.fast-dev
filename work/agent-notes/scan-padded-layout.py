#!/usr/bin/env python3
"""Text-only inventory of fixed Padded literals, not a proof of their semantics."""
from pathlib import Path
import re
import json
root = Path(__file__).resolve().parents[2]
rows = []
pattern = re.compile(r'\[((?:\s*\d+#8\s*,?)*)\]\s*(\d+)')
for path in (root/'submission/InitECandidate/Proofs/BackendStages').glob('Padded[0-9]*.lean'):
    text = path.read_text()
    definition = text[text.index('def Padded'):text.index('theorem Padded')]
    matches = pattern.findall(definition)
    lengths = [len(re.findall(r'\d+#8', bs)) for bs, _ in matches]
    rows.append(dict(section=path.stem, lines=len(lengths), bytes=sum(lengths),
        max_line_bytes=max(lengths, default=0),
        annotated_lengths_agree=lengths == [int(n) for _, n in matches],
        install_token='AsmWithLab.install' in definition))
result = dict(
    scope='Text-only inspection of fixed Padded literals; not a Lean theorem or compilation-equality proof',
    sections=len(rows), encoded_lines=sum(r['lines'] for r in rows),
    bytes=sum(r['bytes'] for r in rows), max_line_bytes=max(r['max_line_bytes'] for r in rows),
    all_annotations_agree=all(r['annotated_lengths_agree'] for r in rows),
    install_tokens=sum(r['install_token'] for r in rows),
    rows=sorted(rows, key=lambda r: int(r['section'][6:])))
(root/'work/agent-notes/padded-layout-scan.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'rows'}, indent=2))
