import InitECandidate.Solver.Input.Requests.DecodedImage
import InitECandidate.Solver.Input.Requests.ByteBudget

namespace InitECandidate.Solver.Input.Requests
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob cursor : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}

theorem DecodedImage.size_number (data : DecodedImage input source blob cursor start size counts) : (BitVec.ofNat 64 size).toNat=size := by
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=data.inside; have b:=data.inputBound; omega)]

/-- Each actual request count consumes precisely its validated slice, without
word subtraction wrapping or a separate independent maximum per list. -/
theorem DecodedImage.list_inside (data : DecodedImage input source blob cursor start size counts) (index : Nat) (inside : index<5) :
    start+(offsetWord input start index).toNat+(counts index).toNat*(elementSize index).toNat≤input.length%2^64 := by
  let words := offsetWord input start
  let total := BitVec.ofNat 64 size
  have totalNumber : total.toNat=size := data.size_number
  have ordered := data.layout.ordered words total index inside
  have span := data.layout.span_number words total index inside
  have bytes := data.image.element_bytes source (blob+BitVec.ofNat 64 start) cursor total words counts index inside
  have upper : boundary words total (index+1)≤size := by
    by_cases more : index+1<5
    · have bounded := (data.layout.valid (index+1) more).2.1
      change (words (index+1)).toNat≤total.toNat at bounded
      simpa only [boundary,if_pos more,totalNumber] using bounded
    · simp only [boundary,if_neg more,totalNumber,Nat.le_refl]
  have initial : boundary words total index=(words index).toNat := by simp only [boundary,if_pos inside]
  have countRange : (offsetWord input start index).toNat+(counts index).toNat*(elementSize index).toNat≤size := by
    calc
      _ = boundary words total index+(countSpan words total index).toNat := by
        rw [initial,Nat.mul_comm (counts index).toNat (elementSize index).toNat,bytes]
      _ = boundary words total (index+1) := by rw [span]; omega
      _ ≤ size := upper
  have raw := data.inside
  omega

theorem DecodedImage.list_arena (data : DecodedImage input source blob cursor start size counts) (index : Nat) (inside : index<5) :
    AllocatedBytes.Arena (blob+BitVec.ofNat 64 start+offsetWord input start index) ((counts index).toNat*(elementSize index).toNat) := by
  have extent := data.list_inside index inside
  have arena := AllocatedBytes.Arena.subrange blob (input.length%2^64) (start+(offsetWord input start index).toNat)
    ((counts index).toNat*(elementSize index).toNat) data.inputArena extent
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using arena

theorem DecodedImage.count_bound (data : DecodedImage input source blob cursor start size counts) (index : Nat) (inside : index<5) :
    (counts index).toNat≤134217728 := by
  have length : 68≤(elementSize index).toNat := by
    have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl <;> decide
  have scaled := Nat.mul_le_mul_right (counts index).toNat length
  have extent := data.list_inside index inside
  have bytes := data.inputBound
  rw [Nat.mul_comm (counts index).toNat] at extent
  omega

/-- All five current request lists share this one actual encoded byte budget. -/
theorem DecodedImage.byte_budget (data : DecodedImage input source blob cursor start size counts) :
    192*(counts 0).toNat+76*(counts 1).toNat+116*(counts 2).toNat+184*(counts 3).toNat+68*(counts 4).toNat+20=size := by
  simpa only [data.size_number] using data.image.byte_budget source (blob+BitVec.ofNat 64 start) cursor (BitVec.ofNat 64 size) (offsetWord input start) counts data.layout

theorem DecodedImage.count_budget (data : DecodedImage input source blob cursor start size counts) :
    (counts 0).toNat+(counts 1).toNat+(counts 2).toNat+(counts 3).toNat+(counts 4).toNat≤(size-20)/68 := by
  simpa only [data.size_number] using data.image.count_budget source (blob+BitVec.ofNat 64 start) cursor (BitVec.ofNat 64 size) (offsetWord input start) counts data.layout

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.size_number
#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.list_inside
#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.list_arena
#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.count_bound
#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.byte_budget
#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.count_budget
