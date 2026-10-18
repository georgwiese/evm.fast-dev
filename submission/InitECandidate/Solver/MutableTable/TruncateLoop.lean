import InitECandidate.Solver.MutableTable.TruncatePost

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def price (kind : KeyHash.Kind) : Nat → Nat
  | 0 => 0
  | count + 1 => price kind count + Delete.modelPrice kind (count + 1) + 2

/-- Quantitative actual truncate loop/return on a covered normal run.
An absent/no-change deletion would stutter back to exactly the same tail
with less clock, contradicting add-clock equality for that normal run.
Thus every taken iteration reduces the physical count by one. -/
theorem tail_non_timeout (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (limit : BitVec 64) (result : Option (PanSemResultExact 64)) (notTimeout : result ≠ some .timeOut) (count : Nat) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (length : slots.length = count) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (enough : price kind count ≤ source.clock)
    (normal : evaluateHOLFiniteState source tail = (result, target)) :
    ∃ paid memory next, paid + price kind (min count limit.toNat) ≤ price kind count ∧ result = some (.returned (.val (.word 0#64))) ∧ ModelPost source kind plan count limit paid memory target next := by
  induction count generalizing source slots with
  | zero =>
    obtain ⟨resultEq, post⟩ := stopped_post_result source target kind plan valid domain slots room header occupied limit (by omega) tableLocal limitLocal result normal
    exact ⟨0, source.memory, slots, by simp [price], resultEq, by simpa only [length] using post⟩
  | succ count ih =>
    by_cases stopped : slots.length ≤ limit.toNat
    · obtain ⟨resultEq, post⟩ := stopped_post_result source target kind plan valid domain slots room header occupied limit stopped tableLocal limitLocal result normal
      exact ⟨0, source.memory, slots, by rw [Nat.min_eq_left (show count + 1 ≤ limit.toNat from by omega), Nat.zero_add], resultEq, by simpa only [length] using post⟩
    · have active : limit.toNat < slots.length := by omega
      have funded : price kind count + Delete.modelPrice kind slots.length + 2 ≤ source.clock := by simpa only [price, length] using enough
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
      obtain ⟨stepPaid, memory, next, flag, stepBound, bodyRun, stepPost⟩ := step_execute entry kind plan valid domain little slots room (by omega) entryModel bits small power header tableLocal strideLocal
        hashCode copyCode memeqCode findCode deleteCode (by change Delete.modelPrice kind slots.length + 1 ≤ source.clock - 1; omega)
      let nextState := Delete.modelCallState entry stepPaid memory
      have test := condition_read source kind plan valid domain slots.length room header limit tableLocal limitLocal
      rw [if_pos active] at test
      have continues := MemeqByteRuntime.loop_continue source nextState condition loopBody returnZero test positive bodyRun
        (by change source.clock - 1 - stepPaid ≤ source.clock - 1; omega)
      change evaluateHOLFiniteState source tail = evaluateHOLFiniteState nextState tail at continues
      have nextNormal : evaluateHOLFiniteState nextState tail = (result, target) := continues.symm.trans normal
      rcases stepPost.shape with ⟨absent, noMemory, noSlots⟩ | ⟨deleted, reduced⟩
      · have sameState : nextState = {source with clock := nextState.clock} := by
          change Delete.modelCallState entry stepPaid memory = {source with clock := source.clock - 1 - stepPaid}
          rw [noMemory]
          rfl
        have strict : nextState.clock < source.clock := by change source.clock - 1 - stepPaid < source.clock; omega
        exact (InitECandidate.Solver.no_clock_stutter source target tail result nextState.clock strict normal notTimeout
          (by rw [← sameState]; exact nextNormal)).elim
      · have nextLength : next.length = count := by omega
        obtain ⟨restPaid, finalMemory, finalSlots, restBound, resultEq, restPost⟩ := ih nextState domain little next nextLength (by omega) stepPost.occupied stepPost.header tableLocal strideLocal limitLocal
          hashCode copyCode memeqCode findCode deleteCode (by change price kind count ≤ source.clock - 1 - stepPaid; omega) nextNormal
        have totalBound : 1 + stepPaid + restPaid + price kind (min (count + 1) limit.toNat) ≤ price kind (count + 1) := by
          change 1 + stepPaid + restPaid + price kind (min (count + 1) limit.toNat) ≤ price kind count + Delete.modelPrice kind (count + 1) + 2
          rw [length] at stepBound
          have within : limit.toNat ≤ count := by omega
          rw [Nat.min_eq_right within] at restBound
          rw [Nat.min_eq_right (show limit.toNat ≤ count + 1 from by omega)]
          omega
        have frameEq : emptyLocalsHOLFinite {nextState with memory := finalMemory, clock := nextState.clock - restPaid} =
            emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - (1 + stepPaid + restPaid)} := by
          change emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - 1 - stepPaid - restPaid} = _
          have subtract : source.clock - 1 - stepPaid - restPaid = source.clock - (1 + stepPaid + restPaid) := by omega
          rw [subtract]
        refine ⟨1 + stepPaid + restPaid, finalMemory, finalSlots, totalBound, resultEq, restPost.frame.trans frameEq, ?_, restPost.header, restPost.occupied,
          TableFootprint.Frame.trans source.memory memory finalMemory kind plan stepPost.footprint restPost.footprint⟩
        have within : limit.toNat ≤ count := by omega
        simpa only [Nat.min_eq_right within, Nat.min_eq_right (show limit.toNat ≤ count + 1 from by omega)] using restPost.length

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.tail_non_timeout
