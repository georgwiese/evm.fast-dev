#!/usr/bin/env python3
"""Retarget named solver lookup proofs to actual Software function positions.

Executable declaration/body definitions are left unchanged. Each resulting
lookup proof still has to establish equality of that body with the current
Software declaration in Lean. Pass --check to audit without writing.
"""
import argparse
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
parser.add_argument('paths', nargs='+', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
software = (root / 'Guest/SoftwareAst.lean').read_text().split('def guestAst : List (Decl (BitVec 64)) :=', 1)[1]
functions = re.findall(r'\bguestFn_[A-Za-z0-9_]+', software)
assert len(functions) == len(set(functions))
positions = {name: index for index, name in enumerate(functions)}
pattern = re.compile(r'((?:Input\.)?OriginalCode\.indexed code installed )\d+( \(GasBudget\.OriginalCodeEnvironment\.originalEntry )Guest\.(?:Software\.)?(guestFn_\w+)(\) \(by rfl\))')
dirty = []
for path in args.paths:
    text = path.read_text()
    revised = text
    matches = list(pattern.finditer(text))
    for match in reversed(matches):
        name = match[3]
        current = 'Guest.Software.' + name
        original = 'Guest.' + name
        end = revised.index('using checked', match.end())
        proof = revised[match.end():end]
        if current not in proof:
            if original not in proof:
                raise ValueError(f'{path}: missing explicit declaration normalization for {name}')
            proof = proof.replace(original, current + ',' + original, 1)
        lookup = match[1] + str(positions[name]) + match[2] + current + match[4]
        revised = revised[:match.start()] + lookup + proof + revised[end:]
    if revised != text:
        dirty.append(str(path))
        if not args.check:
            path.write_text(revised)
    print(f'{path}: {len(matches)} lookup proofs; {"needs retargeting" if revised != text else "current"}')
if args.check and dirty:
    raise SystemExit(1)
