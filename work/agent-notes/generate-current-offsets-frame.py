#!/usr/bin/env python3
"""Generate shared current workspace frames and the legacy five-key interface.

The emitted proofs still require Lean validation; source scanning and string
specialization are not semantic evidence on their own.
"""
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[2]
folder=ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup'
metadata=json.loads((ROOT/'work/agent-notes/current-startup-globals-generation.json').read_text())
def module(name):return ''.join(p[0].upper()+p[1:] for p in name.split('_'))
roots=metadata['roots'][3:]+metadata['extra_roots']
by_module={module(n):n for n in metadata['order']}
sources={};dependencies={}
for name in metadata['order']:
    source=(folder/(module(name)+'.lean')).read_text();sources[name]=source
    dependencies[name]=[by_module[m] for m in re.findall(r'^import InitECandidate\.Solver\.Input\.CurrentStartup\.(\w+)$',source,re.M) if m in by_module]
seen=set();order=[]
def visit(name):
    if name in seen:return
    assert name!='ssz_init','The selected graph changes the protected offsets global'
    for child in dependencies[name]:visit(child)
    seen.add(name);order.append(name)
for name in roots:visit(name)
text='''import InitECandidate.Solver.Input.CurrentStartup.Base
import InitECandidate.Solver.Input.GlobalEffectsCaught

namespace InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive WorkspaceKey where | offsets | lengthChunk | zeroHashes | keccakState | keccakPad

def workspaceKey : WorkspaceKey → MlS
  | .offsets => ofString "ssz_offs"
  | .lengthChunk => ofString "ssz_len_chunk"
  | .zeroHashes => ofString "zero_hashes"
  | .keccakState => ofString "keccak_st"
  | .keccakPad => ofString "keccak_pad"

-- Actual-syntax effects for all three SSZ workspace globals. The default keeps
-- the existing offsets API. No initializer success or readable buffer is assumed.
'''
inputs=[]
for name in order:
    source=sources[name];path=folder/(module(name)+'.lean')
    inputs.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    if 'theorem any_key ' in source:
        proof=source.split('theorem any_key ',1)[1].split(' := by\n',1)[1].split('\ntheorem preserves ',1)[0]
        proof=proof.replace('selected','(workspaceKey workspace)')
    else:
        proof=source.split('theorem preserves ',1)[1].split(' := by\n',1)[1].split('\nend '+module(name),1)[0]
        proof=proof.replace('(key cursor)','(workspaceKey workspace)').replace('(by cases cursor <;> decide)','(by cases workspace <;> decide)')
    for child in order:
        proof=proof.replace(module(child)+'.preserves cursor code installed',child+' code installed workspace')
        proof=proof.replace(module(child)+'.any_key (workspaceKey workspace) code installed',child+' code installed workspace')
        proof=proof.replace(module(child)+'.any_key (workspaceKey workspace) code',child+' code installed workspace')
    assert 'cursor' not in proof and 'any_key' not in proof,(name,proof)
    text+=f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem {name} (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .{name}) := by
'''+proof
text+='\nend InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame\n\n'
text+=''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.{name}\n' for name in order)
# Keep the large proofs in a single six-key core. mpt_init writes the new key,
# so its restricted proof stays in the original five-key compatibility module.
header, rest = text.split('\nset_option maxRecDepth', 1)
body = ('set_option maxRecDepth' + rest).split('\nend InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame', 1)[0]
blocks = [b for b in re.split(r'(?=set_option maxRecDepth 100000 in\nset_option maxHeartbeats 4000000 in\ntheorem )', body) if b.strip()]
names = [re.search(r'theorem (\w+)', b)[1] for b in blocks]
assert names == order
keys = header[:header.index('-- Actual-syntax')].replace('import InitECandidate.Solver.Input.GlobalEffectsCaught\n', '')
keys += 'end InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame\n'
core = header.replace('import InitECandidate.Solver.Input.CurrentStartup.Base', 'import InitECandidate.Solver.Input.CurrentStartup.OffsetsKeys').replace('CurrentStartup.OffsetsFrame', 'CurrentStartup.WorkspaceFrameCore').replace('| keccakPad\n', '| keccakPad | mptHash\n').replace('  | .keccakPad => ofString "keccak_pad"', '  | .keccakPad => ofString "keccak_pad"\n  | .mptHash => ofString "mpt_hash_scratch"')
core = core[:core.index('-- Actual-syntax')] + '''/-- Shared current-syntax frames, including the MPT buffer after its initializer. -/
def fromLegacy : OffsetsFrame.WorkspaceKey → WorkspaceKey
  | .offsets => .offsets
  | .lengthChunk => .lengthChunk
  | .zeroHashes => .zeroHashes
  | .keccakState => .keccakState
  | .keccakPad => .keccakPad

@[simp] theorem workspaceKey_fromLegacy (key : OffsetsFrame.WorkspaceKey) :
    workspaceKey (fromLegacy key) = OffsetsFrame.workspaceKey key := by
  cases key <;> rfl
'''
core += '\n' + ''.join(b for n, b in zip(names, blocks) if n != 'mpt_init')
core += '\nend InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore\n\n'
core += ''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore.{n}\n' for n in names if n != 'mpt_init')
wrappers = '''import InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrameCore

namespace InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

-- Preserve the five-key public API. The shared six-key proofs live in the core;
-- mpt_init has its own restricted proof because it initializes the sixth key.
'''
for n, b in zip(names, blocks):
    if n == 'mpt_init':
        wrappers += '\n' + b
    else:
        wrappers += f'''
theorem {n} (code) (installed : OriginalCode.Installed code) (workspace : WorkspaceKey := .offsets) :
    GlobalEffects.Preserves (workspaceKey workspace) code (Code.body .{n}) := by
  simpa only [WorkspaceFrameCore.workspaceKey_fromLegacy] using
    WorkspaceFrameCore.{n} code installed (WorkspaceFrameCore.fromLegacy workspace)
'''
wrappers += '\nend InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame\n\n\n'
wrappers += ''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame.{n}\n' for n in names)
outputs = {'OffsetsKeys.lean': keys, 'WorkspaceFrameCore.lean': core, 'OffsetsFrame.lean': wrappers}
import sys
check = '--check' in sys.argv
for name, source in outputs.items():
    path = folder / name
    if check:
        assert path.read_text().strip() == source.strip(), f'Generated layout differs: {path}'
    else:
        path.write_text(source)
report = {'fixed_source': 'Guest/SoftwareAst.lean',
          'fixed_source_sha256': hashlib.sha256((ROOT/'Guest/SoftwareAst.lean').read_bytes()).hexdigest(),
          'roots': roots, 'order': order, 'inputs': inputs,
          'generated_sources': [{'path': str((folder/name).relative_to(ROOT)),
                                 'sha256': hashlib.sha256((folder/name).read_bytes()).hexdigest()} for name in outputs],
          'protected_globals': ['ssz_offs', 'ssz_len_chunk', 'zero_hashes', 'keccak_st', 'keccak_pad', 'mpt_hash_scratch'],
          'restricted_initializer': 'mpt_init preserves only the original five keys',
          'scope': 'Generated actual all-outcome global frames; not proof validation, ownership or a runtime bound.'}
if not check:
    (ROOT/'work/agent-notes/current-offsets-frame-generation.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'helpers': len(order), 'shared_helpers': len(order)-1, 'check_only': check}))
