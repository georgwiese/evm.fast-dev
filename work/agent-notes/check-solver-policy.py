#!/usr/bin/env python3
"""Incremental local policy check; fixed sources rely on the prior policy pass.

Does not run the full verifier, axiom audit, comparator or kernel replay.
"""
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'verifier'))
import check_submission as policy

root = ROOT / 'submission'
files = sorted(root.rglob('*'))
modules = {'.'.join(p.relative_to(root).with_suffix('').parts)
           for p in files if p.is_file() and p.suffix == '.lean'}
contracts = policy.contract_modules(ROOT)
errors = []
total = 0
for path in files:
    if path.is_symlink() or not (path.is_file() or path.is_dir()):
        errors.append(f'{path}: forbidden file type')
    if path.is_file():
        size = path.stat().st_size
        total += size
        if size > policy.MAX_FILE_BYTES:
            errors.append(f'{path}: exceeds file size limit')
if len(files) > policy.MAX_FILES or total > policy.MAX_TOTAL_BYTES:
    errors.append('Package size/entry limit exceeded')
checked = []
for path in sorted((root / 'InitECandidate/Solver').rglob('*.lean')):
    checked.append(str(path.relative_to(ROOT)))
    source = path.read_text()
    try:
        for module in policy.imports(source):
            if module in contracts or module in modules or any(
                module == lib or module.startswith(lib + '.') for lib in policy.ALLOWED_LIBRARIES):
                continue
            errors.append(f'{path}: forbidden import {module}')
        if re.search(r'\b(sorry|admit|native_decide|axiom)\b', policy.strip_comments(source)):
            errors.append(f'{path}: unfinished proof or additional trusted declaration')
    except ValueError as exc:
        errors.append(f'{path}: {exc}')
record = {
    'ok': not errors,
    'scope': 'Incremental import/token check of all Solver files using verifier/check_submission.py imports and allowed modules; whole-tree entry/size checks; fixed files rely on prior full policy pass',
    'prior_full_policy': 'logs/submission-policy.log',
    'checked_files': checked, 'package_entries': len(files), 'package_bytes': total,
    'claim': policy.claim(root / 'claim.json'), 'errors': errors,
    'not_a_full_verification': True,
}
(ROOT / 'work/agent-notes/policy-check.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: v for k, v in record.items() if k not in {'checked_files', 'scope'}}))
sys.exit(bool(errors))
