import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Data returned by the original resolver: either an actual node or a
bounded next slice, with genuine input provenance for retained hash pointers. -/
def ResolveResult (post : PanSemStateFiniteExact 64 Guest.HostMemory) (db heap : BitVec 64) (value : ValueHOL 64) : Prop:=
  (value=.rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]) ∨
  (value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
    AllocatedBytes.Arena heap 32 ∧ post.memory heap=.word 0#64 ∧
    (∃ hash,2713731432≤hash.toNat ∧ hash.toNat+32≤db.toNat ∧ post.memory (heap+24#64)=.word hash) ∧
    ∃ finalHeap,post.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
      AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat+32≤finalHeap.toNat) ∨
  ∃ nextPointer nextLength pending,
    value=.rStruct [.val (.word 1#64),.val (.word nextPointer),.val (.word nextLength),.val (.word pending)] ∧
    nextLength.toNat≤1024 ∧ 2713731432≤nextPointer.toNat ∧ nextPointer.toNat+nextLength.toNat≤db.toNat ∧
    (pending=0#64 ∨ 2713731432≤pending.toNat ∧ pending.toNat+32≤db.toNat)

theorem ResolveResult.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (db heap : BitVec 64) (value : ValueHOL 64)
    (result : ResolveResult source db heap value) (memory : target.memory=source.memory) (globals : target.globals=source.globals) : ResolveResult target db heap value := by
  simpa only [ResolveResult,memory,globals] using result

/-- The actual HASH scratch store below the incoming heap retains every
field of a real terminal hash allocation and all bounded-input results. -/
theorem ResolveResult.store_below (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db heap address word : BitVec 64) (value : ValueHOL 64)
    (result : ResolveResult source db heap value) (below : address.toNat<heap.toNat) :
    ResolveResult {source with memory:=StoreWord.put source.memory address word} db heap value := by
  rcases result with empty|⟨valueEq,arena,tag,hashData,finalHeap,heapCell,heapArena,aligned,before⟩|decode
  · exact Or.inl empty
  · have away : heap≠address := by intro equal; have numeric:=congrArg BitVec.toNat equal; omega
    have number : (heap+24#64).toNat=heap.toNat+24 := byteAddress_toNat heap 24 (by have bound:=arena.upper; omega)
    have cacheAway : heap+24#64≠address := by intro equal; have numeric:=congrArg BitVec.toNat equal; rw [number] at numeric; omega
    obtain ⟨hash,lower,upper,stored⟩:=hashData
    exact Or.inr (Or.inl ⟨valueEq,arena,(if_neg away).trans tag,⟨hash,lower,upper,(if_neg cacheAway).trans stored⟩,
      finalHeap,heapCell,heapArena,aligned,before⟩)
  · exact Or.inr (Or.inr decode)

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveResult.of_fields
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveResult.store_below
