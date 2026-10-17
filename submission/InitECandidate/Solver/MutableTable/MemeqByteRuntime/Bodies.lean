import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Program
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def blockWords (bytes : Nat → UInt8) (index : Nat) (offset : Fin 8) : BitVec 64 :=
  BitVec.ofNat 64 (bytes (index + offset.val)).toNat

theorem block_ready {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (inputs : Inputs source a b length left right)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index + 8 ≤ length) :
    ∀ check ∈ Memeq32.byteChecks (blockWords left index) (blockWords right index), CompareChain.Ready source check := by
  have reads (offset : Fin 8) :
      CompareChain.Ready source ⟨Memeq32.byteAt "a" offset.val, Memeq32.byteAt "b" offset.val,
        blockWords left index offset, blockWords right index offset⟩ := by
    have offsetInside : index + offset.val < length := by have bound := offset.isLt; omega
    have leftRead : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be
        (a + BitVec.ofNat 64 index + BitVec.ofNat 64 offset.val) = some (left (index + offset.val)) := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using inputs.leftRead _ offsetInside
    have rightRead : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be
        (b + BitVec.ofNat 64 index + BitVec.ofNat 64 offset.val) = some (right (index + offset.val)) := by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using inputs.rightRead _ offsetInside
    exact ⟨Memeq32.eval_byteAt source "a" a (BitVec.ofNat 64 index) offset.val _ inputs.aLocal current leftRead,
      Memeq32.eval_byteAt source "b" b (BitVec.ofNat 64 index) offset.val _ inputs.bLocal current rightRead⟩
  intro check member
  simp only [Memeq32.byteChecks, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reads 0
  · exact reads 1
  · exact reads 2
  · exact reads 3
  · exact reads 4
  · exact reads 5
  · exact reads 6
  · exact reads 7

/-- Actual eight-byte comparison body from arbitrary mapped input bytes.
Either it increments i by8 or returns mismatch, with no body clocks/writes. -/
theorem block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (inputs : Inputs source a b length left right)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index + 8 ≤ length) :
    evaluateHOLFiniteState source blockBody =
      if CompareChain.agrees (Memeq32.byteChecks (blockWords left index) (blockWords right index)) then
        (none, WitnessRadix.QueryBranch.bind source "i" (BitVec.ofNat 64 index + 8#64)) else
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) :=
  Memeq32.byte_body_execute source (BitVec.ofNat 64 index) _ _ current
    (block_ready source a b length index left right inputs current inside)

/-- Actual trailing-byte body. Its source loop pays one clock per byte. -/
theorem byte_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (inputs : Inputs source a b length left right)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (inside : index < length) :
    evaluateHOLFiniteState source byteBody =
      if CompareChain.agrees (byteChecks (left index) (right index)) then
        (none, WitnessRadix.QueryBranch.bind source "i" (BitVec.ofNat 64 index + 1#64)) else
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  have ready : ∀ check ∈ byteChecks (left index) (right index), CompareChain.Ready source check := by
    intro check member
    simp only [byteChecks, List.mem_cons, List.not_mem_nil, or_false] at member
    subst check
    exact ⟨Memeq32.eval_byteAt source "a" a (BitVec.ofNat 64 index) 0 _ inputs.aLocal current
        (by simpa only [BitVec.add_zero] using inputs.leftRead index inside),
      Memeq32.eval_byteAt source "b" b (BitVec.ofNat 64 index) 0 _ inputs.bLocal current
        (by simpa only [BitVec.add_zero] using inputs.rightRead index inside)⟩
  have incrementRun := StateSteps.assign_execute source "i" (addConst (localVar "i") 1#64)
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 index + 1#64) current (by
      simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, current,
        valueIsWord, valueWord, wordOpHOL, wordOp])
  change evaluateHOLFiniteState source increment1 = _ at incrementRun
  rw [byte_body_shape (left index) (right index), CompareChain.execute_prefix source _ increment1 ready, incrementRun]

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.block_ready
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.block_execute
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.byte_execute
