#!/usr/bin/env python3
"""Reuse generated actual-syntax proofs for the precheck read-only host frame.

The translated proof terms still have to type-check against the actual fixed
code and source oracle. This script provides no proof validation by itself.
"""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[2]
folder=ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup'
order=['ssz_fail','host_input_byte','host_input_le32','ssz_check_offsets','precheck_host_ssz_header']
def module(name):return ''.join(p[0].upper()+p[1:] for p in name.split('_'))
text='''import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.ReadHostScoped

namespace InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated actual-syntax proof terms; Lean must validate the source oracle
-- and every all-outcome call/loop composition. Events need not be unchanged.
'''
inputs=[]
for name in order:
    path=folder/(module(name)+'.lean')
    source=path.read_text();inputs.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    proof=source.split('theorem any_key ',1)[1].split(' := by\n',1)[1].split('\ntheorem preserves ',1)[0]
    proof=proof.replace('GlobalEffects.', 'ReadHostEffects.').replace(' selected code',' code')
    for child in order:
        proof=proof.replace(module(child)+'.any_key code installed',child+' code installed')
    assert 'selected' not in proof and 'any_key' not in proof,(name,proof)
    assert 'shared_store' not in proof and 'external' not in proof
    text+=f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem {name} (code) (installed : OriginalCode.Installed code) :
    ReadHostEffects.Preserves code (Code.body .{name}) := by
'''+proof
text+='\nend InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck\n\n'
text+=''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.ReadOnlyPrecheck.{name}\n' for name in order)
path=folder/'PrecheckHostFrame.lean';path.write_text(text)
report={'fixed_source':'Guest/SoftwareAst.lean','fixed_source_sha256':hashlib.sha256((ROOT/'Guest/SoftwareAst.lean').read_bytes()).hexdigest(),
        'inputs':inputs,'order':order,'generated_source':str(path.relative_to(ROOT)),'generated_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'scope':'Generated proof terms, not validation; all-outcome host bytes equality under the actual source oracle, not event equality or runtime.'}
(ROOT/'work/agent-notes/current-precheck-host-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'helpers':len(order),'generated_source':report['generated_source'],'generated_sha256':report['generated_sha256']}))
