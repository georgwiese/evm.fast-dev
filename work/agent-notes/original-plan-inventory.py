#!/usr/bin/env python3
"""Offline inventory for the unchanged-program bound; not verification."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PREFIX = 'InitECandidate.Solver.'
BASE = ROOT / 'submission/InitECandidate/Solver'
modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts[1:]): p for p in BASE.rglob('*.lean')}
imports = {m: re.findall(r'^import\s+(\S+)', p.read_text(), re.M) for m, p in modules.items()}
missing_imports = [(m, d) for m, deps in imports.items() for d in deps
                   if d.startswith(PREFIX) and d not in modules]
assert not missing_imports, missing_imports
seeds = {PREFIX+'WitnessRadix.RawProgram', PREFIX+'WitnessRadix.BuildProgram'}
affected = seeds & set(modules)
while True:
    updated = affected | {m for m, deps in imports.items() if any(d in affected for d in deps)}
    if updated == affected:
        break
    affected = updated

roots = {
    'baseline_bootstrap': ['BootstrapStartup'],
    'original_witness_constructor': ['MutableTable.WitnessBuildExecution', 'MutableTable.WitnessBuildEmpty'],
    'original_witness_lookup': ['MutableTable.WitnessDictionaryLookup', 'MutableTable.NodeDbDictionary32'],
    'original_mutable_key_operations': ['MutableTable.HashSizedMapped', 'MutableTable.MemeqSizedMapped', 'MutableTable.MemeqByteRuntime.Call', 'MutableTable.FindSizedCall', 'MutableTable.GetSizedCall', 'MutableTable.HasSizedCall', 'MutableTable.HashByteRuntime.Call', 'MutableTable.MemeqByteRuntime.AlignedMapped', 'MutableTable.GetOtherCall', 'MutableTable.HasOtherCall', 'MutableTable.InsertGeneralCall'],
    'input_reachability': ['Input.Witness.BodyNormal', 'Input.Witness.PrefixNormal', 'Input.RequestStoredGasFromHeader', 'Input.RlpLength.BlockGuard'],
    'local_gas_accounting': ['GasBudget.StateChargeBudget', 'GasBudget.ForwardSites', 'GasBudget.ChildError', 'GasBudget.ChildSuccess'],
    'original_root_initialization': ['GasBudget.RootMsgNormal', 'GasBudget.FrameOpenCall', 'Input.FreshRecordCall'],
    'abstract_global_accounting': ['GasBudget.BlockAccounting', 'GasBudget.MergeBudget', 'GasBudget.NestedDecay', 'GasBudget.StorageDebt'],
    'compiled_local_work': ['GuestWork.GasAccounting', 'GuestWork.ExtendMemoryAllocTransfer', 'GuestWork.FrameAllocBounded'],
}
for family in roots.values():
    for name in family:
        assert PREFIX+name in modules, name

def closure(root):
    seen = set()
    stack = [root]
    while stack:
        node = stack.pop()
        if node in seen or node not in modules:
            continue
        seen.add(node)
        stack.extend(imports[node])
    return seen

reference = '7d656e5b6878aa420de793d9d6f689fa26ec0842'
frozen_changes = subprocess.check_output([
    'git', 'diff', '--name-only', reference, '--', 'Guest', 'InitE',
    'submission/Solution.lean', 'submission/claim.json', 'submission/InitECandidate',
    ':(exclude)submission/InitECandidate/Solver',
], cwd=ROOT, text=True).splitlines()
assert not frozen_changes, frozen_changes
fixed = ['Guest/Ast.lean', 'Guest/guest.pp.pnk', 'submission/Solution.lean', 'submission/claim.json']
identity = {}
for path in fixed:
    actual = (ROOT/path).read_bytes()
    baseline = subprocess.check_output(['git', 'show', f'{reference}:{path}'], cwd=ROOT)
    assert actual == baseline, f'Baseline changed: {path}'
    identity[path] = hashlib.sha256(actual).hexdigest()

report = {
    'objective': 'Reasonably tight finite bound for the unchanged implementation; no numerical ceiling.',
    'reference': reference,
    'fixed_files_sha256': identity,
    'frozen_source_semantics_rom_and_proofs_unchanged': not frozen_changes,
    'scope': 'Dependency and obligation inventory only; neither whole-program bound nor verification.',
    'solver_modules': len(modules),
    'missing_solver_imports': missing_imports,
    'module_families': dict(sorted(Counter(m.split('.')[2] for m in modules).items())),
    'original_roots': {family: [dict(module=name, solver_dependency_count=len(closure(PREFIX+name)),
                                   imports_replacement_ast=PREFIX+name in affected)
                              for name in names] for family, names in roots.items()},
    'replacement_ast_reverse_closure_count': len(affected),
    'replacement_ast_modules_present': sorted(seeds & set(modules)),
    'affected_families': dict(sorted(Counter(m.split('.')[2] for m in affected).items())),
    'cleanup_bridges': [
        'Separate generic state/local helpers from candidate lookup proofs.',
        'Separate generic loop traversal from candidate construction AST.',
        'Separate declaration execution from candidate helper entry.',
        'Use original constructor syntax/capacity definitions, independent of candidate RawProgram.',
        'Remove replacement-only result-format imports from original dictionary lookup.',
    ],
    'open_global_obligations': [
        'Reachable entry/code/arena/clock facts for original decoder, headers and dictionaries.',
        'Actual executed regular/state gas conservation across roots, calls, successful merges, rollback and block counters.',
        'Aggregate original mutable-map probes, growth, deletion, copies and phase sharing.',
        'Actual persistent allocation or path-progress charging for cumulative trie/witness queries, including scoped lifetimes.',
        'Whole-entry weighted work, compiler premises and existing baseline evaluator transport.',
    ],
    'not_completion_metrics': ['Module counts', 'Dependency counts', 'Previous replacement-plan percentages'],
}
(ROOT/'work/agent-notes/original-plan-inventory.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'solver_modules': len(modules), 'replacement_ast_reverse_closure': len(affected),
                  'original_roots_importing_replacement_ast': sum(r['imports_replacement_ast'] for rows in report['original_roots'].values() for r in rows),
                  'fixed_files_unchanged': True}))
