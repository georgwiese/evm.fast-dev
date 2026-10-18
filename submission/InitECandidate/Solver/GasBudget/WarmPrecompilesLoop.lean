import InitECandidate.Solver.GasBudget.WarmPrecompilesStep

namespace InitECandidate.Solver.GasBudget.WarmPrecompiles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def price (count remaining : Nat) : Nat := (9 * count + 13) * remaining + 9 * WitnessBuild.triangle remaining
theorem price_step (count remaining : Nat) : price count (remaining + 1) = 9 * count + 13 + price (count + 1) remaining := by
  simp only [price, WitnessBuild.triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega
theorem price_mono (first second remaining : Nat) (bounded : first ≤ second) : price first remaining ≤ price second remaining := by
  have bound := Nat.mul_le_mul_right remaining (show 9 * first + 13 ≤ 9 * second + 13 from by omega)
  exact Nat.add_le_add_right bound _

/-- Entire actual 18-address precompile warming loop. Population room rules
out every growth, so layout, heap and all other globals remain unchanged.
All words outside the real table pools survive. -/
theorem loop_normal (remaining : Nat) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start index cursor : Nat) (plan : Plan) (slots : List Nat)
    (inputValid : MemoryRegion.Valid ⟨start, 360⟩) (count : index + remaining = 18)
    (environment : WarmKeys.Environment source) (valid : Valid .account plan) (capacity : plan.capacity = 64)
    (spare : slots.length + remaining ≤ 32) (earlier : ∀ pool, plan.base pool + size .account plan pool ≤ cursor)
    (cursorBound : cursor ≤ 33806089496) (cursorAligned : cursor % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (header : MemoryModel.Header source.memory .account plan (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source .account plan slots)
    (locals : Locals source (cell plan .header 0) start index)
    (normal : evaluateHOLFiniteState source loop = (none, target)) :
    ∃ paid nextSlots, paid ≤ price slots.length remaining ∧ paid ≤ source.clock ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := source.clock - paid} ∧
      MemoryModel.Header target.memory .account plan (BitVec.ofNat 64 nextSlots.length) ∧ MemoryModel.Occupied target .account plan nextSlots ∧
      Locals target (cell plan .header 0) start 18 ∧ slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + remaining ∧
      TableFootprint.Frame source.memory target.memory .account plan := by
  induction remaining generalizing source index slots with
  | zero =>
    have finished : index = 18 := by omega
    have test := condition_read source _ start index (by omega) locals
    rw [if_neg (by omega)] at test
    simp only [eval] at test
    have actual : evaluateHOLFiniteState source loop = (none, source) := by
      rw [loop, evaluateHOLFiniteState_while_total]
      simp only [evalHOLFinite, test]
      simp
    have same := congrArg Prod.snd (normal.symm.trans actual)
    change target = source at same
    subst target
    refine ⟨0, slots, by simp [price, WitnessBuild.triangle], by omega, by simp only [Nat.sub_zero], header, occupied,
      by simpa only [finished] using locals, by omega, by omega, TableFootprint.Frame.refl _ _ _⟩
  | succ remaining ih =>
    have active : index < 18 := by omega
    have test := condition_read source _ start index (by omega) locals
    rw [if_pos active] at test
    obtain ⟨positive, middle, bodyRun, tailRun, clockBound⟩ := Input.while_none_step source target (ofString "m") condition loopBody body_safe test normal
    let entry := decClockHOLFinite source
    have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
    have entryModel := MemoryModel.Occupied.of_fields source entry .account plan slots occupied rfl rfl rfl
    obtain ⟨paid, middleSlots, bounded, fits, frame, middleHeader, middleModel, middleLocals, lower, upper, footprint⟩ :=
      body_normal entry middle start index cursor plan slots inputValid active entryEnvironment valid capacity (by omega) earlier cursorBound cursorAligned heap header entryModel (locals.of_fields rfl rfl) bodyRun
    have codes := congrArg PanSemStateFiniteExact.code frame
    have domain := congrArg PanSemStateFiniteExact.memaddrs frame
    have endian := congrArg PanSemStateFiniteExact.be frame
    have globals := congrArg PanSemStateFiniteExact.globals frame
    have clock := congrArg PanSemStateFiniteExact.clock frame
    change middle.code = source.code at codes
    change middle.memaddrs = source.memaddrs at domain
    change middle.be = source.be at endian
    change middle.globals = source.globals at globals
    change middle.clock = source.clock - 1 - paid at clock
    change paid ≤ source.clock - 1 at fits
    have middleEnvironment : WarmKeys.Environment middle := environment.of_fields codes domain endian
    have middleHeap : middle.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) := by rw [globals]; exact heap
    obtain ⟨restPaid, finalSlots, restBound, restFits, restFrame, finalHeader, finalModel, finalLocals, finalLower, finalUpper, finalFootprint⟩ :=
      ih (source := middle) (index := index + 1) (slots := middleSlots) (by omega) middleEnvironment (by omega) middleHeap middleHeader middleModel middleLocals tailRun
    have monotone := price_mono middleSlots.length (slots.length + 1) remaining upper
    have totalBound : 1 + paid + restPaid ≤ price slots.length (remaining + 1) := by rw [price_step]; omega
    have composite := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := target.memory, clock := middle.clock - restPaid}) frame
    change emptyLocalsHOLFinite {middle with memory := target.memory, clock := middle.clock - restPaid} =
      emptyLocalsHOLFinite {source with memory := target.memory, clock := middle.clock - restPaid} at composite
    have finalFrame := restFrame.trans composite
    have subtract : middle.clock - restPaid = source.clock - (1 + paid + restPaid) := by omega
    rw [subtract] at finalFrame
    refine ⟨1 + paid + restPaid, finalSlots, totalBound, by omega, finalFrame, finalHeader, finalModel, finalLocals,
      by omega, by omega, TableFootprint.Frame.trans source.memory middle.memory target.memory .account plan footprint finalFootprint⟩

end InitECandidate.Solver.GasBudget.WarmPrecompiles

#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.price_step
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.price_mono
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.loop_normal
