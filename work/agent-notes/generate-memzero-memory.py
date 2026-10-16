#!/usr/bin/env python3
"""Emit a structural memory-summary proof for the actual fixed Named78 DAG.

The script is untrusted scaffolding. Every constructor application and literal
zero/store adjacency is checked again by Lean against the fixed definitions.
"""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
source=(root/'submission/InitECandidate/Proofs/BackendStages/Named78.lean').read_text()
defs={int(i):body.strip() for i,body in re.findall(r'def NamedBody78_(\d+) : StackLang.HolProg 64 :=\n(.*?)(?=\ndef |\Z)',source,re.S)}
top=int(re.search(r'def Named78 :.*?NamedBody78_(\d+)\)',source,re.S)[1])
def children(i):return [int(x) for x in re.findall(r'NamedBody78_(\d+)',defs[i])]
pairs=[]
def emit(i,indent='  '):
 d=defs[i]; cs=children(i)
 if d.startswith('.seq'):
  first,tail=cs
  const=re.search(r'HolInst.const (\d+) 0#64',defs[first])
  skip=False; storeseq=tail
  if defs[tail].startswith('.seq'):
   a,b=children(tail)
   if defs[a].endswith('.skip'):
    skip=True;storeseq=b
  if const and defs[storeseq].startswith('.seq'):
   store,rest=children(storeseq)
   match=re.search(r'HolInst.mem Flapjack.WordMemOp.(store8|store) (\d+)',defs[store])
   if match and match[2]==const[1]:
    pairs.append((first,store))
    prefix=indent+'apply Clears.skipAfter\n' if skip else ''
    name='byteStoreThen' if match[1]=='store8' else 'wordStoreThen'
    return prefix+indent+f'apply Clears.{name}\n'+emit(rest,indent)
  return indent+'apply Clears.seq\n'+indent+'·\n'+emit(first,indent+'  ')+indent+'·\n'+emit(tail,indent+'  ')
 if d.startswith('.ite'):
  a,b=cs
  return indent+'apply Clears.ite\n'+indent+'·\n'+emit(a,indent+'  ')+indent+'·\n'+emit(b,indent+'  ')
 if d.startswith('.loop'):
  return indent+'apply Clears.loop\n'+emit(cs[0],indent)
 assert 'HolInst.mem' not in d,(i,d)
 return indent+'exact Clears.leaf _ (by decide)\n'
proof=emit(top)
text='''import InitECandidate.Solver.GuestWork.ZeroStoreProgram
import InitECandidate.Proofs.BackendStages.Named78

namespace InitECandidate.Solver.GuestWork.MemzeroMemory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open ZeroMemory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The complete fixed memzero routine never increases an existing word's
unsigned value. Covers all executions, including failed stores and timeouts;
no alignment, address separation, initial registers or length bound is assumed. -/
theorem clears {C F : Type} : Clears (C := C) (F := F) Named78.2 := by
'''+proof+'''
/-- A saved word length remains a word below its original upper bound across
an actual memzero execution, even when the zeroing region overlaps that slot. -/
theorem saved_length {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (address : BitVec 64) (maximum : Nat)
    (bounded : ∃ value, source.memory address = .word value ∧ value.toNat ≤ maximum)
    (execution : evaluate (Named78.2, source) = (result, post)) :
    ∃ value, post.memory address = .word value ∧ value.toNat ≤ maximum := by
  have below := clears source
  rw [execution] at below
  exact below.bound address maximum bounded

end InitECandidate.Solver.GuestWork.MemzeroMemory
#print axioms InitECandidate.Solver.GuestWork.MemzeroMemory.clears
#print axioms InitECandidate.Solver.GuestWork.MemzeroMemory.saved_length
'''
(root/'submission/InitECandidate/Solver/GuestWork/MemzeroMemory.lean').write_text(text)
print({'zero_store_pairs':len(pairs),'pairs':pairs,'top':top})
