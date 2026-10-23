import InitECandidate.Solver.Mpt.SetProgram
import InitECandidate.Solver.Mpt.NibbleKeyGeneralCall

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real original setter enters its root declaration with the actual
key tuple for either secure flag. Its genuine scoped execution supplies
the query and paid clock; both lexical and physical nonlocal frames are
retained for the later whole-function composition. -/
theorem general_key_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m flag key stp pad hash heap : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word flag)
    (hashCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word hash)))
    (data : Keccak256.EntryData source stp key pad hash length)
    (hashArena : AllocatedBytes.Arena hash 32) (hashBefore : hash.toNat+32≤heap.toNat)
    (inputArena : AllocatedBytes.Arena key length) (inputBefore : key.toNat+length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ current inner,AllocatedBytes.Arena heap (NibbleKey.nibbleLength flag length) ∧
      current.locals.lookup (ofString "nk")=some (NibbleKey.nibbleValue heap (NibbleKey.nibbleLength flag length)) ∧
      (∀ other,ofString "nk"≠other→current.locals.lookup other=source.locals.lookup other) ∧
      TrieWalk.KeyView current.memory current.memaddrs current.be heap (NibbleKey.nibbleLength flag length) ∧
      source.clock-current.clock≤218 ∧
      KeccakAbsorb.hashControl current=KeccakAbsorb.hashControl (PersistentAlloc.post source heap (BitVec.ofNat 64 (NibbleKey.nibbleLength flag length))) ∧
      (∀ query : BitVec 64,Keccak256.Protected stp pad hash query→
        (query.toNat<heap.toNat ∨ heap.toNat+NibbleKey.nibbleLength flag length≤query.toNat)→current.memory query=source.memory query) ∧
      target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧
      evaluateHOLFiniteState current afterKey=(some (.returned value),inner) := by
  obtain ⟨current,inner,trace,clock,continued⟩:=key_trace source target value normal
  have erased:=trace.erase afterKey
  simp only [actions,Input.CallPrefix.program] at erased
  rw [←body_shape,normal,continued] at erased
  obtain ⟨middle,first,last⟩:=trace.head
  have same : current=middle:=by cases last; rfl
  subst current
  obtain ⟨arena,nk,saved,view,cost,frame,memory⟩:=NibbleKey.scoped_general_normal (ofString "nk") keyArguments m flag key stp pad hash heap length small installed domain little
    (key_arguments source m key length mCell keyCell lengthCell) mapped cell hashCell data hashArena hashBefore inputArena inputBefore heapCell frontier aligned first
  exact ⟨middle,inner,arena,nk,saved,view,cost,frame,memory,clock,erased,continued⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.general_key_entry
