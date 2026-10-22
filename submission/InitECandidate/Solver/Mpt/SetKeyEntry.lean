import InitECandidate.Solver.Mpt.SetProgram

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original setter reaches its mutation dispatch with the
actual freshly converted key, retained caller ABI and real continuation.
The physical key and heap facts are derived from its current input model. -/
theorem key_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m key heap : BitVec 64) (length : Nat)
    (small : length≤32) (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (inputArena : AllocatedBytes.Arena key length) (before : key.toNat+length≤heap.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ current inner,AllocatedBytes.Arena heap (2*length) ∧
      current.locals.lookup (ofString "nk")=some (NibbleKey.output heap length) ∧
      (∀ other,ofString "nk"≠other→current.locals.lookup other=source.locals.lookup other) ∧
      TrieWalk.KeyView current.memory current.memaddrs current.be heap (2*length) ∧
      source.clock-current.clock≤length/4+6 ∧
      KeyToNibbles.writeMetadata current=KeyToNibbles.writeMetadata (PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+2*length≤query.toNat→current.memory query=source.memory query) ∧
      target.clock=inner.clock ∧ evaluateHOLFiniteState current afterKey=(some (.returned value),inner) := by
  obtain ⟨current,inner,trace,endpoint,continued⟩:=key_trace source target value normal
  obtain ⟨middle,first,last⟩:=trace.head
  have same : current=middle:=by cases last; rfl
  subst current
  obtain ⟨arena,nk,saved,view,cost,frame,memory⟩:=NibbleKey.scoped_normal (ofString "nk") keyArguments m key heap length small installed domain little
    (key_arguments source m key length mCell keyCell lengthCell) mapped cell heapCell frontier aligned inputArena before first
  exact ⟨middle,inner,arena,nk,saved,view,cost,frame,memory,endpoint,continued⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.key_entry
