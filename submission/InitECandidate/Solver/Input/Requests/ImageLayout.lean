import InitECandidate.Solver.Input.Requests.CountLocals
import InitECandidate.Solver.Input.OffsetsAnyLoop

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Physical original request arrays and their actual element counts. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer cursor total : BitVec 64) (words counts : Nat → BitVec 64) : Prop where
  cells : ∀ index < 5,source.memory (cursor + BitVec.ofNat 64 (16*index)) = .word (pointer + words index) ∧
    source.memory (cursor + BitVec.ofNat 64 (16*index+8)) = .word (counts index)
  arithmetic : ∀ index < 5,(counts index).toNat = (countSpan words total index).toNat / (elementSize index).toNat ∧
    (countSpan words total index).toNat % (elementSize index).toNat = 0


structure Layout (words : Nat → BitVec 64) (total : BitVec 64) : Prop where
  first : words 0 = 20#64
  valid : ∀ index < 5,Offsets.ValidAt 20#64 total words index

/-- A proved frame of the ten actual record fields transports its complete
physical image; count/layout arithmetic is independent of memory state. -/
theorem Image.of_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer cursor total : BitVec 64} {words counts : Nat→BitVec 64}
    (data : Image source pointer cursor total words counts)
    (frame : ∀ index<5, post.memory (cursor+BitVec.ofNat 64 (16*index))=source.memory (cursor+BitVec.ofNat 64 (16*index)) ∧
      post.memory (cursor+BitVec.ofNat 64 (16*index+8))=source.memory (cursor+BitVec.ofNat 64 (16*index+8))) : Image post pointer cursor total words counts := by
  refine ⟨?_,data.arithmetic⟩
  intro index inside
  have cells := data.cells index inside
  have memory := frame index inside
  exact ⟨memory.1.trans cells.1,memory.2.trans cells.2⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.Image.of_memory
