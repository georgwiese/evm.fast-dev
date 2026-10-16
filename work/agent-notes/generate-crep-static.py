#!/usr/bin/env python3
"""Generate ordinary Lean-decide checks of the fixed Crep syntax ceiling.

The planning scan selects the candidate bound; only completed Lean builds prove
it. The final module connects the chunk list to the actual compiler output list.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'submission/InitECandidate/Solver/CrepStatic'
OUT.mkdir(exist_ok=True)
NS = 'InitECandidate.Solver.CrepStatic'
scan = json.loads((ROOT / 'work/agent-notes/crep-ceiling-dag.json').read_text())
limit = scan['maximum_scanned_ceiling']
assert [r['procedure'] for r in scan['procedures']] == list(range(826))
umbrella = (ROOT / 'submission/InitECandidate/Proofs/FrontendStages/Crep/FunctionsFacts.lean').read_text()
outputs = re.search(r'^def outputs : .*? := (\[.*?\])\s*\ntheorem', umbrella, re.M | re.S)
assert outputs and list(map(int,re.findall(r'output(\d+)',outputs[1]))) == list(range(826))
def write(path, content):
    if not path.exists() or path.read_text() != content:
        path.write_text(content)
for record in scan['procedures']:
    n = record['procedure']
    literal = ROOT / f'submission/InitECandidate/Proofs/FrontendStages/Crep/Data{n}.lean'
    assert hashlib.sha256(literal.read_bytes()).hexdigest() == record['sha256']
    write(OUT / f'Procedure{n}.lean', f'''import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import InitECandidate.Proofs.CrepKernelComputation
import InitECandidate.Proofs.FrontendStages.Crep.Data{n}

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem ceiling{n} : ceiling output{n}.2.2 ≤ {limit} := by
  dsimp only [output{n}]
  rw [InitECandidate.Proofs.CrepKernelComputation.crepProgToHOL_function_eq]
  decide

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.ceiling{n}
''')
for i,start in enumerate(range(0,826,16)):
    ids = range(start,min(start+16,826))
    imports='\n'.join(f'import {NS}.Procedure{n}' for n in ids)
    entries=', '.join(f'output{n}' for n in ids)
    terms=[f'decide (ceiling output{n}.2.2 ≤ {limit})' for n in ids]
    goal=' && ('.join(terms)+' && true'+')'*(len(terms)-1)
    facts=', '.join(f'ceiling{n}' for n in ids)
    write(OUT / f'Chunk{i}.lean',f'''{imports}
import InitECandidate.Solver.CrepToLoopBound.CheckCode

namespace {NS}
open Flapjack InitECandidate.Solver.CrepToLoopBound
open InitECandidate.Proofs.FrontendStages.Crep
set_option maxRecDepth 100000

def chunk{i} : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := [{entries}]

theorem chunk{i}Safe : entriesSafe {limit} chunk{i} = true := by
  change ({goal}) = true
  simp only [{facts}, decide_true, Bool.true_and]

end {NS}
#print axioms {NS}.chunk{i}Safe
''')
imports='\n'.join(f'import {NS}.Chunk{i}' for i in range(52))
entries=' ++ ('.join(f'chunk{i}' for i in range(52))+' ++ []'+')'*51
facts=', '.join(f'chunk{i}Safe' for i in range(52))
write(OUT/'Programs.lean',f'''{imports}

namespace {NS}
open Flapjack InitECandidate.Solver.CrepToLoopBound
set_option maxRecDepth 100000

def crepProgram : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64) := {entries}

theorem crepProgramSafe : entriesSafe {limit} crepProgram = true := by
  simp only [entriesSafe, crepProgram, List.all_append, List.all_nil,
    {facts}, Bool.and_true]

theorem crepCodeSafe : CodeSafe {limit} (alistToFmapCodeExact crepProgram) :=
  entriesSafe_codeSafe {limit} crepProgram crepProgramSafe

end {NS}
#print axioms {NS}.crepProgramSafe
#print axioms {NS}.crepCodeSafe
''')
write(OUT/'Fixed.lean',f'''import {NS}.Programs
import InitECandidate.Proofs.FrontendStages.Crep.FunctionsFacts

namespace {NS}
open Flapjack InitECandidate.Solver.CrepToLoopBound
set_option maxRecDepth 100000

theorem crepProgram_eq_outputs :
    crepProgram = InitECandidate.Proofs.FrontendStages.Crep.outputs := by rfl

theorem fixedCrepCodeSafe : CodeSafe {limit}
    (alistToFmapCodeExact InitECandidate.Proofs.FrontendStages.Crep.outputs) := by
  rw [← crepProgram_eq_outputs]
  exact crepCodeSafe

theorem fixedSimplifiedCrepCodeSafe {{F : Type}} (source : CrepSemHOLState 64 F)
    (code : source.code = alistToFmapCodeExact InitECandidate.Proofs.FrontendStages.Crep.outputs) :
    CodeSafe {limit} (crepSimpMapcsHOL source).code := by
  apply codeSafe_simplify {limit} source
  rw [code]
  exact fixedCrepCodeSafe

end {NS}
#print axioms {NS}.crepProgram_eq_outputs
#print axioms {NS}.fixedCrepCodeSafe
#print axioms {NS}.fixedSimplifiedCrepCodeSafe
''')
print(json.dumps({'procedures':826,'chunks':52,'candidate_limit':limit,'checked':False}))
