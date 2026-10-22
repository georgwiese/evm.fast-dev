import InitECandidate.Solver.Mpt.NibbleKeyConvert

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original mpt_nibble_key on a current unsecured trie. Its real
normal return derives the fresh allocation, actual nibble view, heap update,
protected old memory and source cost. No future allocation room or clock
funding is supplied. -/
theorem unsecured_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m key heap : BitVec 64) (length : Nat)
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
    AllocatedBytes.Arena heap (2*length) ∧ value=output heap length ∧
      TrieWalk.KeyView target.memory target.memaddrs target.be heap (2*length) ∧
      source.clock-target.clock≤length/4+5 ∧
      KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata (PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))) ∧
      ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+2*length≤query.toNat→target.memory query=source.memory query := by
  obtain ⟨arena,inner,continued,endpoint⟩:=normal_allocation source target m heap length small installed mCell lengthCell mapped cell heapCell frontier value normal
  obtain ⟨currentKey,currentLength,currentOut⟩:=allocated_locals source key heap length keyCell lengthCell
  obtain ⟨answer,view,cost,frame,memory⟩:=tail_normal (allocated source heap length) inner key heap length small installed domain little
    currentKey currentLength currentOut inputArena arena aligned before value continued
  have clock:=allocated_clock source heap length
  refine ⟨arena,answer,?_,?_,?_,?_⟩
  · rw [endpoint]
    exact view
  · rw [endpoint]
    change (allocated source heap length).clock-inner.clock≤length/4+4 at cost
    change source.clock-inner.clock≤length/4+5
    rw [clock] at cost
    omega
  · rw [endpoint]
    exact frame
  · intro query away
    rw [endpoint]
    exact memory query away

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.unsecured_normal
