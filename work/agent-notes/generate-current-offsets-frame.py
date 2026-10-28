#!/usr/bin/env python3
"""Specialize actual-syntax effects to the three SSZ globals outside ssz_init.

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

inductive WorkspaceKey where | offsets | lengthChunk | zeroHashes

def workspaceKey : WorkspaceKey → MlS
  | .offsets => ofString "ssz_offs"
  | .lengthChunk => ofString "ssz_len_chunk"
  | .zeroHashes => ofString "zero_hashes"

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
path=folder/'OffsetsFrame.lean';path.write_text(text)
report={'fixed_source':'Guest/SoftwareAst.lean','fixed_source_sha256':hashlib.sha256((ROOT/'Guest/SoftwareAst.lean').read_bytes()).hexdigest(),
        'roots':roots,'order':order,'inputs':inputs,'generated_source':str(path.relative_to(ROOT)),'generated_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'protected_globals':['ssz_offs','ssz_len_chunk','zero_hashes'],
        'scope':'Generated all-outcome SSZ global frames with default offsets API; not proof validation, allocation geometry, host/memory equality or a runtime bound.'}
(ROOT/'work/agent-notes/current-offsets-frame-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'helpers':len(order),'generated_source':report['generated_source'],'generated_sha256':report['generated_sha256']}))
