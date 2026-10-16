#!/usr/bin/env python3
"""Generate all-clock Work and timeout proofs against the immutable allocator DAG.
The generator is untrusted scaffolding; Lean checks the emitted source.
"""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
fixed=(root/'submission/InitECandidate/Proofs/BackendStages/Named71.lean').read_text()
defs={int(i):b.strip() for i,b in re.findall(r'def NamedBody71_(\d+) : StackLang.HolProg 64 :=\n(.*?)(?=\ndef |\Z)',fixed,re.S)}
def children(i): return [int(x) for x in re.findall(r'NamedBody71_(\d+)',defs[i])]
def basic(i):
    if defs[i].startswith(('.seq','.ite')): return all(basic(x) for x in children(i))
    return '.call' not in defs[i]
def nodes(i): return 1+sum(nodes(x) for x in children(i))
def ticks(i):
    if defs[i].startswith('.seq'): return sum(ticks(x) for x in children(i))
    if defs[i].startswith('.ite'): return max(ticks(x) for x in children(i))
    return int(defs[i].endswith('.tick'))
def cost(i):
    if basic(i): return nodes(i)+ticks(i)
    if defs[i].startswith('.seq'): return sum(cost(x) for x in children(i))
    assert i in [91,178]
    return 1+cost(children(i)[1])
entry=(root/'submission/InitECandidate/Solver/GuestWork/FrameAllocEntry.lean').read_text()
ns=entry[entry.index('namespace '):entry.index('/-- The actual successful')]
ns=ns.replace('set_option maxRecDepth','set_option linter.unusedSimpArgs false\nset_option maxRecDepth')
head=entry[entry.index('theorem updates'):entry.index('    (enoughClock :')]
head=head.replace('theorem updates','theorem work_all_clocks').replace('(source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))','(source : StackSemStateFiniteExact 64 C F)')
initial=entry[entry.index('  have roundedGuard'):entry.index('  have zero :')]
args=entry[entry.index('  simp [Named71')+8:entry.index('] at execution')].replace('zero, one, two, three,','clock,')
params='metadata offset heap globals stack pointer scratch amount returnLabel returnOffset'
fields='hmetadata hheap hstack hamount hreturn stackSafe metadataDomain metadataValue globalsEq pointerDomain pointerValue scratchDomain scratchValue saveDomain metadataNotSave scratchNotSave fits roundedFits'
count=0
def proof(i,indent):
    global count
    if basic(i): return indent+'exact Work.basic (by decide)\n'
    if defs[i].startswith('.ite'):
        return indent+f'apply Work.ite (credits := {cost(i)-1})\n'+indent+'· intro chosen\n'+indent+'  simp [branchChoice, StackSemStateOps.getVar, StackSemStateOps.getVarImm,\n'+indent+'    HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, mask,\n'+indent+'    fits, roundedGuard, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at chosen\n'+indent+'· intro _\n'+indent+'  exact Work.basic (by decide)\n'
    a,b=children(i);count+=1;k=count
    return (indent+f'refine Work.seq (firstCredit := {cost(a)}) (secondCredit := {cost(b)}) ?_ ?_\n'+
        indent+'·\n'+proof(a,indent+'  ')+indent+f'· intro state{k} run{k}\n'+
        indent+'  simp ['+args.replace('\n    ', '\n'+indent+'    ')+f'] at run{k}\n'+indent+'  all_goals\n'+
        indent+f'    subst state{k}\n'+proof(b,indent+'    '))
text='import InitECandidate.Solver.GuestWork.FrameAllocBounded\nimport InitECandidate.Solver.FlattenWeighted.BlockBound\n\n'+ns
text+='/-- Actual allocator Work bound under its valid-call guards, for every initial clock. -/\n'+head+' : Work Named71.2 source 58 := by\n'+initial
text+='  by_cases enough : 4 ≤ source.clock\n  · exact work source '+params+'\n      '+fields+' enough\n'
text+='  · have options : source.clock = 0 ∨ source.clock = 1 ∨ source.clock = 2 ∨ source.clock = 3 := by omega\n    rcases options with clock | clock | clock | clock\n    all_goals\n'+proof(220,'      ')
text+='''
/-- Every insufficient-clock allocator run times out with no remaining clock. -/
theorem small_timeout {C F : Type}
    (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (valid : Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
    (smallClock : source.clock < 4) :
    (evaluate (Named71.2, source)).1 = some .timeOut ∧
    (evaluate (Named71.2, source)).2.clock = 0 := by
  obtain ⟨FIELDS⟩ := valid
INITIAL
  have options : source.clock = 0 ∨ source.clock = 1 ∨ source.clock = 2 ∨ source.clock = 3 := by omega
  rcases options with clock | clock | clock | clock
  all_goals
    simp [ARGS, emptyEnv]

end InitECandidate.Solver.GuestWork.FrameAllocEntry
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.work_all_clocks
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.small_timeout
'''.replace('FIELDS',', '.join(fields.split())).replace('INITIAL',initial.rstrip()).replace('ARGS',args)
(root/'submission/InitECandidate/Solver/GuestWork/FrameAllocAllClocks.lean').write_text(text)
print({'work':cost(220),'sequence_nodes':count})
