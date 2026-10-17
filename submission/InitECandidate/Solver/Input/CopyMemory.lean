import InitECandidate.Solver.Input.CopyWalk

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact

/-- Exact untouched-cell frame for the actual repeated host-read/store state. -/
theorem walk_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index rounds : Nat)
    (away : ∀ slot<rounds,query≠pointer+BitVec.ofNat 64 (index+8*slot)) :
    (walk source pointer index rounds).memory query=source.memory query := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    rw [walk,ih _ _ (by
      intro slot inside
      have absent:=away (slot+1) (by omega)
      have arithmetic : index+8*(slot+1)=index+8+8*slot := by omega
      rw [arithmetic] at absent
      exact absent)]
    have absent:=away 0 (by omega)
    simp only [Nat.mul_zero,Nat.add_zero] at absent
    change WitnessRadix.StoreWord.put source.memory (pointer+BitVec.ofNat 64 index)
      (Guest.wordOfLeBytes (SharedRead.bytes source.ffi.ffiState (Guest.inputDataAddr+BitVec.ofNat 64 index))) query=source.memory query
    simp [WitnessRadix.StoreWord.put,absent]

/-- Every copied heap word equals its actual host word. Distinct destinations
follow from the natural allocation range, rather than an assumed array model. -/
theorem walk_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index rounds slot : Nat)
    (inside : slot<rounds) (fits : pointer.toNat+index+8*rounds<2^64) :
    (walk source pointer index rounds).memory (pointer+BitVec.ofNat 64 (index+8*slot))=
      .word (Guest.wordOfLeBytes (SharedRead.bytes source.ffi.ffiState
        (Guest.inputDataAddr+BitVec.ofNat 64 (index+8*slot)))) := by
  induction rounds generalizing source index slot with
  | zero => omega
  | succ rounds ih =>
    simp only [Nat.mul_succ] at fits
    let next:=wordPost (decClockHOLFinite source) pointer (BitVec.ofNat 64 index)
    cases slot with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero]
      rw [walk,walk_away next pointer (pointer+BitVec.ofNat 64 index) (index+8) rounds (by
        intro slot member same
        have head:=WitnessRadix.MemoryBytes.offset_toNat pointer index (by omega)
        have tail:=WitnessRadix.MemoryBytes.offset_toNat pointer (index+8+8*slot) (by omega)
        have numbers:=congrArg BitVec.toNat same
        rw [head,tail] at numbers
        omega)]
      change WitnessRadix.StoreWord.put source.memory (pointer+BitVec.ofNat 64 index) _
        (pointer+BitVec.ofNat 64 index)=_
      simp only [WitnessRadix.StoreWord.put,↓reduceIte]
      rfl
    | succ slot =>
      have arithmetic : index+8*(slot+1)=index+8+8*slot := by omega
      rw [arithmetic,walk]
      exact ih next (index+8) slot (by omega) (by omega)

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.walk_away
#print axioms InitECandidate.Solver.Input.Blob.walk_cell
