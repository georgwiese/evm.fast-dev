import InitECandidate.Solver.MutableTable.KeysLocals

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rowPrice (kind : KeyHash.Kind) : Nat := stride kind / 8 + 1

/-- One actual key-enumeration body iteration, before its enclosing while
clock. The original padded-stride memcpy preserves every source table pool
and every word outside the output reservation. Both counters advance. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (start : Nat) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (outValid : MemoryRegion.Valid (outputRegion kind start slots.length))
    (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ start) (index : Nat) (active : index < slots.length)
    (locals : Locals source kind plan start slots.length index)
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : rowPrice kind ≤ source.clock) :
    ∃ paid memory, paid ≤ rowPrice kind ∧ evaluateHOLFiniteState source loopBody = (none, nextState source memory paid index) ∧
      MemoryModel.PoolFrame source.memory memory kind plan ∧
      MemoryModel.Occupied (nextState source memory paid index) kind plan slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ start + stride kind * slots.length + 8 ≤ query.toNat → memory query = source.memory query) := by
  let ordinal : Fin slots.length := ⟨index, active⟩
  let slot := slots.get ordinal
  let entered := bind source "slot" (BitVec.ofNat 64 slot)
  let src := MemoryRegion.pointer (keyRegion kind plan slot)
  let dst := MemoryRegion.pointer (destinationRegion kind start index)
  let paid := CopyGeneral.cost src dst (stride kind) + 1
  let memory := CopyGeneral.resultMemory source.memory source.be src dst (stride kind)
  let copied := CopyGeneral.callState entered src dst (stride kind)
  let canonical := {source with memory := memory, clock := source.clock - paid}
  have countBound := MemoryModel.Occupied.length_le source kind plan slots occupied
  have indexInside : index < plan.capacity := Nat.lt_of_lt_of_le active countBound
  have slotInside : slot < plan.capacity := occupied.inside _ (List.get_mem slots ordinal)
  have orderMapped : source.memaddrs (cell plan .order 0 + BitVec.ofNat 64 index * 8#64) := by
    rw [Delete.Move.natural_word_address kind plan valid .order index indexInside, domain]
    exact mapped kind plan valid .order _ (by change 8 * index < 8 * plan.capacity; omega) (by omega)
  have orderStored : source.memory (cell plan .order 0 + BitVec.ofNat 64 index * 8#64) = .word (BitVec.ofNat 64 slot) := by
    rw [Delete.Move.natural_word_address kind plan valid .order index indexInside]
    exact occupied.order ordinal
  have orderReadRun : eval source orderRead = some (.val (.word (BitVec.ofNat 64 slot))) := by
    simpa only [orderRead, Delete.wordAddress, Delete.scaled] using Delete.Move.word_read source "order" "i" _ _ (BitVec.ofNat 64 slot) locals.order locals.index orderMapped orderStored
  have enteredLocals := Locals.bind_slot source kind plan start slots.length index slot locals
  have copyBound : paid ≤ rowPrice kind := by
    have bound := CopyMapped.cost_le_price src dst (stride kind)
    simp only [MemeqByteRuntime.price, (stride_bounds kind).2.2, Nat.add_zero] at bound
    exact Nat.add_le_add_right bound 1
  have copyRun := CopyGeneral.call_execute entered _ src dst (stride kind) (copy_arguments entered kind plan start slots.length index slot enteredLocals (bind_lookup_same _ _ _)) copyCode
    (copy_regions entered kind plan valid domain start slots.length index slot outValid active slotInside)
    (by cases kind <;> decide) (Nat.le_trans copyBound enough)
  have tailRun := after_copy_execute copied kind plan start slots.length index (Locals.of_locals entered copied kind plan start slots.length index enteredLocals rfl)
  have inner : evaluateHOLFiniteState entered (.seq copyCall afterCopy) = (none, nextState copied copied.memory 0 index) := by
    rw [StateSteps.next_sequence entered copied copyCall afterCopy copyRun (Nat.sub_le _ _), tailRun]
  have scopeRun := Input.ScalarScope.declare_execute source _ "slot" orderRead (BitVec.ofNat 64 slot) (.seq copyCall afterCopy) none orderReadRun inner
  have copiedEq : copied = bind canonical "slot" (BitVec.ofNat 64 slot) := rfl
  have restored : restore source "slot" (nextState copied copied.memory 0 index) = nextState source memory paid index := by
    simp only [nextState, Nat.sub_zero]
    change restore source "slot" (bind (bind copied "k" (BitVec.ofNat 64 (index + 1))) "i" (BitVec.ofNat 64 (index + 1))) = _
    rw [restore_bind_other source _ "slot" "i" _ (by decide), restore_bind_other source copied "slot" "k" _ (by decide), copiedEq]
    change bind (bind (restore canonical "slot" (bind canonical "slot" (BitVec.ofNat 64 slot))) "k" _) "i" _ = _
    rw [restore_bound]
  have tableFrame := copy_preserves_table source kind plan valid start slots.length index slot outValid active earlier
  refine ⟨paid, memory, copyBound, ?_, tableFrame, ?_, ?_⟩
  · simpa only [loopBody, restored] using scopeRun
  · exact MemoryModel.Occupied.of_pool_frame source _ kind plan valid slots occupied rfl rfl tableFrame
  · intro query outside
    apply CopyGeneral.resultMemory_away
    apply MemoryRegion.copy_away (destinationRegion kind start index) (destination_region_valid kind start slots.length index outValid active) _ (Nat.le_refl _)
    have full : stride kind * index + stride kind ≤ stride kind * slots.length := by
      have bound := Nat.mul_le_mul_left (stride kind) (Nat.succ_le_of_lt active)
      simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] using bound
    rcases outside with before | after
    · left; change query.toNat < start + stride kind * index; omega
    · right; change start + stride kind * index + stride kind ≤ query.toNat; omega

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.step_execute
