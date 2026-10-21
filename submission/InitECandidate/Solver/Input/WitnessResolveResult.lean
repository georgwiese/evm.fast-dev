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

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveResult.of_fields
