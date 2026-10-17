import InitECandidate.Solver.MutableTable.HashByteRuntime.Bodies
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Blocks

namespace InitECandidate.Solver.MutableTable.HashByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix
open MemeqByteRuntime (loop_continue loop_stop price price_step price_small)

/-- The actual trailing-byte hash loop finishes after exactly the remaining
bytes; every load/fold is derived from input reads. -/
theorem tail_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer hash : BitVec 64) (length index : Nat)
    (bytes : Nat → UInt8) (inputs : Inputs source pointer length bytes)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word hash)))
    (small : length ≤ 64) (inside : index ≤ length) (enough : length - index ≤ source.clock) :
    ∃ digest, evaluateHOLFiniteState source tailProgram =
      (some (.returned (.val (.word digest))), emptyLocalsHOLFinite {source with clock := source.clock - (length - index)}) := by
  generalize rankEq : length - index = rank
  induction rank generalizing source index hash with
  | zero =>
    have done : index = length := by omega
    have test := condition1_read source index length small inside current inputs.lengthLocal
    have stopped : eval source condition1 = some (.val (.word 0#64)) := by simpa only [done, Nat.lt_irrefl, ↓reduceIte] using test
    refine ⟨finalWord hash, ?_⟩
    rw [tail_shape, loop_stop source condition1 byteBody finish stopped, finish_execute source hash hLocal]
    simp only [Nat.sub_zero]
  | succ rank ih =>
    have active : index < length := by omega
    have positive : source.clock ≠ 0 := by omega
    have test := condition1_read source index length small inside current inputs.lengthLocal
    have entering : eval source condition1 = some (.val (.word 1#64)) := by simpa only [if_pos active] using test
    let entry := decClockHOLFinite source
    have entryInputs : Inputs entry pointer length bytes := ⟨inputs.pointerLocal, inputs.lengthLocal, inputs.wTyped, inputs.reads⟩
    let next := byteNext entry index hash (bytes index)
    have bodyRun : evaluateHOLFiniteState entry byteBody = (none, next) := byte_execute entry pointer hash length index bytes entryInputs current hLocal active
    have nextCurrent : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
      change (some (.val (.word (BitVec.ofNat 64 index + 1#64))) : Option (ValueHOL 64)) = _
      rw [BitVec.ofNat_add]
    have nextHash : next.locals.lookup (ofString "h") = some (.val (.word (hash ^^^ BitVec.ofNat 64 (bytes index).toNat))) :=
      (bind_lookup_other _ "i" "h" _ (by decide)).trans (bind_lookup_same _ _ _)
    obtain ⟨digest, recursive⟩ := ih next (hash ^^^ BitVec.ofNat 64 (bytes index).toNat) (index + 1)
      (entryInputs.byte_next index hash (bytes index)) nextCurrent nextHash (by omega)
      (by change length - (index + 1) ≤ source.clock - 1; omega) (by omega)
    have step := loop_continue source next condition1 byteBody finish entering positive bodyRun (Nat.le_refl _)
    rw [← tail_shape] at step
    rw [recursive] at step
    refine ⟨digest, step.trans ?_⟩
    have subtract : source.clock - 1 - rank = source.clock - (rank + 1) := by omega
    change ((some (.returned (.val (.word digest))) : Option (PanSemResultExact 64)), emptyLocalsHOLFinite {source with clock := source.clock - 1 - rank}) = _
    rw [subtract]

/-- Both real generic hash loops and avalanche return. They consume exactly
length/8 + length%8 clocks from index0; alignment is irrelevant here. -/
theorem blocks_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer hash : BitVec 64) (length index : Nat)
    (bytes : Nat → UInt8) (inputs : Inputs source pointer length bytes)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (hLocal : source.locals.lookup (ofString "h") = some (.val (.word hash)))
    (small : length ≤ 64) (inside : index ≤ length) (enough : price (length - index) ≤ source.clock) :
    ∃ digest, evaluateHOLFiniteState source program =
      (some (.returned (.val (.word digest))), emptyLocalsHOLFinite {source with clock := source.clock - price (length - index)}) := by
  generalize rankEq : length - index = rank
  induction rank using Nat.strongRecOn generalizing source index hash with
  | ind rank ih =>
    rw [rankEq] at enough
    have test := condition8_read source index length small inside current inputs.lengthLocal
    by_cases active : index + 8 ≤ length
    · have entering : eval source condition8 = some (.val (.word 1#64)) := by simpa only [if_pos active] using test
      have priceStep : price (length - index) = price (length - (index + 8)) + 1 := by
        have decrement : length - (index + 8) = (length - index) - 8 := by omega
        rw [decrement]
        exact price_step _ (by omega)
      rw [rankEq] at priceStep
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      have entryInputs : Inputs entry pointer length bytes := ⟨inputs.pointerLocal, inputs.lengthLocal, inputs.wTyped, inputs.reads⟩
      let word := blockWord bytes index
      let next := blockNext entry index hash word
      have bodyRun : evaluateHOLFiniteState entry blockBody = (none, next) := block_execute entry pointer hash length index bytes entryInputs current hLocal active
      have nextCurrent : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 8)))) := by
        change (some (.val (.word (BitVec.ofNat 64 index + 8#64))) : Option (ValueHOL 64)) = _
        rw [BitVec.ofNat_add]
      have nextHash : next.locals.lookup (ofString "h") = some (.val (.word (hash ^^^ word))) :=
        (bind_lookup_other _ "i" "h" _ (by decide)).trans (bind_lookup_same _ _ _)
      obtain ⟨digest, recursive⟩ := ih (length - (index + 8)) (by omega) next (hash ^^^ word) (index + 8)
        (entryInputs.block_next index hash word) nextCurrent nextHash active
        (by change price (length - (index + 8)) ≤ source.clock - 1; omega) rfl
      have step := loop_continue source next condition8 blockBody tailProgram entering positive bodyRun (Nat.le_refl _)
      rw [← program_shape] at step
      rw [recursive] at step
      refine ⟨digest, step.trans ?_⟩
      have subtract : source.clock - 1 - price (length - (index + 8)) = source.clock - price rank := by omega
      change ((some (.returned (.val (.word digest))) : Option (PanSemResultExact 64)), emptyLocalsHOLFinite {source with clock := source.clock - 1 - price (length - (index + 8))}) = _
      rw [subtract]
    · have stopped : eval source condition8 = some (.val (.word 0#64)) := by simpa only [if_neg active] using test
      have cost : price (length - index) = length - index := price_small _ (by omega)
      rw [rankEq] at cost
      obtain ⟨digest, recursive⟩ := tail_execute source pointer hash length index bytes inputs current hLocal small inside (by rw [rankEq, ← cost]; exact enough)
      refine ⟨digest, ?_⟩
      rw [program_shape, loop_stop source condition8 blockBody tailProgram stopped, recursive, rankEq, cost]

end InitECandidate.Solver.MutableTable.HashByteRuntime

#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.tail_execute
#print axioms InitECandidate.Solver.MutableTable.HashByteRuntime.blocks_execute
