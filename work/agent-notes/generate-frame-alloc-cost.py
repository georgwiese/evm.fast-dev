#!/usr/bin/env python3
"""Emit a selected-path Work derivation for the fixed Named71 allocator."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
source=(root/'submission/InitECandidate/Proofs/BackendStages/Named71.lean').read_text()
defs={int(i): body.strip() for i,body in re.findall(r'def NamedBody71_(\d+) : StackLang.HolProg 64 :=\n(.*?)(?=\ndef |\Z)', source,re.S)}
def children(i): return [int(x) for x in re.findall(r'NamedBody71_(\d+)',defs[i])]
def basic(i):
    d=defs[i]
    if d.startswith('.seq') or d.startswith('.ite'): return all(basic(x) for x in children(i))
    return '.call' not in d

def nodes(i): return 1+sum(nodes(c) for c in children(i))
def ticks(i):
    d=defs[i]; cs=children(i)
    if d.startswith('.seq'): return sum(ticks(c) for c in cs)
    if d.startswith('.ite'): return max(ticks(c) for c in cs)
    return int(d.endswith('.tick'))
def cost(i):
    if basic(i): return nodes(i)+ticks(i)
    if defs[i].startswith('.seq'): return sum(cost(c) for c in children(i))
    assert i in [91,178]
    return 1+cost(children(i)[1])
entry=(root/'submission/InitECandidate/Solver/GuestWork/FrameAllocEntry.lean').read_text()
prefix=entry[:entry.index('/-- The actual successful')]
prefix=prefix[prefix.index('namespace '):].replace('set_option maxRecDepth', 'set_option linter.unusedSimpArgs false\nset_option maxRecDepth')
header=entry[entry.index('theorem updates'):entry.index('    (execution :')].replace('theorem updates','theorem work').replace('(source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))','(source : StackSemStateFiniteExact 64 C F)')
initial=entry[entry.index('  have roundedGuard'):entry.index('  simp [Named71')]
args=entry[entry.index('  simp [Named71')+8:entry.index('] at execution')]
count=0
def proof(i,indent='  '):
    global count
    if basic(i): return indent+'exact Work.basic (by decide)\n'
    if defs[i].startswith('.ite'):
        return indent+f'apply Work.ite (credits := {cost(i)-1})\n'+indent+'· intro chosen\n'+indent+'  simp [branchChoice, StackSemStateOps.getVar, StackSemStateOps.getVarImm,\n'+indent+'    HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, mask,\n'+indent+'    fits, roundedGuard, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at chosen\n'+indent+'· intro _\n'+indent+'  exact Work.basic (by decide)\n'
    a,b=children(i); count+=1; k=count
    out=indent+f'refine Work.seq (firstCredit := {cost(a)}) (secondCredit := {cost(b)}) ?_ ?_\n'
    out+=indent+'·\n'+proof(a,indent+'  ')
    out+=indent+f'· intro state{k} run{k}\n'
    out+=indent+'  simp ['+args+f'] at run{k}\n'
    out+=indent+f'  subst state{k}\n'
    out+=proof(b,indent+'  ')
    return out
text='import InitECandidate.Solver.GuestWork.FrameAllocEntry\n\n'+prefix
text+='/-- Work bound for the actual successful allocator path, including its prologue. -/\n'+header+f' : Work Named71.2 source {cost(220)} := by\n'+initial+proof(220)
text+='\nend InitECandidate.Solver.GuestWork.FrameAllocEntry\n#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.work\n'
(root/'submission/InitECandidate/Solver/GuestWork/FrameAllocCost.lean').write_text(text)
print({'work':cost(220),'seq_steps':count})
