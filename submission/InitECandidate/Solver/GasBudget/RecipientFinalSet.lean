import InitECandidate.Solver.GasBudget.RecipientLinks
import InitECandidate.Solver.GasBudget.LiveTableSetter

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

/-- The final actual recipient warm-up, including the flag store and both
table-pointer stores. The account insertion may grow across the storage
table; its physical model and the root gas word remain live. -/
theorem final_set_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (plan reader : Plan) (slots readerSlots : List Nat) (cursor floor readerFloor messageStart : Nat)
    (recipient gas : BitVec 64) (environment : WarmKeys.Environment source)
    (table : TableState source .account plan slots cursor floor)
    (readerTable : TableState source .storage reader readerSlots cursor readerFloor)
    (apart : ∀ first second, plan.base first + size .account plan first ≤ reader.base second ∨ reader.base second + size .storage reader second ≤ plan.base first)
    (region : MemoryRegion.Valid ⟨messageStart, 176⟩) (before : messageStart + 176 ≤ floor)
    (readerLater : ∀ pool, messageStart + 176 ≤ reader.base pool)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))))
    (aaLocal : source.locals.lookup (ofString "aa") = some (.val (.word (cell plan .header 0))))
    (akLocal : source.locals.lookup (ofString "ak") = some (.val (.word (cell reader .header 0))))
    (recipientCell : source.memory (BitVec.ofNat 64 messageStart + 32#64) = .word recipient)
    (gasCell : source.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas)
    (queryFits : recipient.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress recipient offset)))
    (normal : evaluateHOLFiniteState source afterChoice = (some (.returned value), post)) :
    ∃ paid nextPlan nextSlots nextCursor ready,
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ Set.noGrowthPrice .account slots.length + 1 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState ready .account nextPlan nextSlots nextCursor floor ∧ TableState ready .storage reader readerSlots nextCursor readerFloor ∧
      (∀ first second, nextPlan.base first + size .account nextPlan first ≤ reader.base second ∨ reader.base second + size .storage reader second ≤ nextPlan.base first) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧ nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      cell nextPlan .header 0 = cell plan .header 0 ∧ ready.locals = source.locals ∧ ready.code = source.code ∧ WarmKeys.Environment ready ∧
      ready.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas ∧
      ready.memory (BitVec.ofNat 64 messageStart + 152#64) = .word (cell nextPlan .header 0) ∧
      ready.memory (BitVec.ofNat 64 messageStart + 160#64) = .word (cell reader .header 0) ∧
      evaluateHOLFiniteState ready messageSite = (some (.returned value), post) ∧
      ∀ query : BitVec 64, query.toNat < messageStart → ready.memory query = source.memory query := by
  let flagged := MessageField.putState source messageStart 136 1#64
  have flagRun := MessageField.scalar_execute source messageStart 136 1#64 (.const 1#64) region (by decide) (by decide) environment.domain messageLocal rfl
  have accountLater : ∀ pool, messageStart + 176 ≤ plan.base pool := by
    intro pool
    have lower := table.lower pool
    omega
  have flaggedTable := MessageField.scalar_table source .account plan slots cursor floor messageStart 136 1#64 table region (by decide) accountLater
  have flaggedReader := MessageField.scalar_table source .storage reader readerSlots cursor readerFloor messageStart 136 1#64 readerTable region (by decide) readerLater
  rw [after_choice_shape,
    StateSteps.next_sequence source source .skip _ (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _),
    StateSteps.next_sequence source flagged _ _ flagRun (Nat.le_refl _)] at normal
  have safe : Input.LocalPrefix (ofString "m") finalSet := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨called, setRun, restRun, _⟩ := safe.normal_continue flagged post afterRecipient value normal
  have recipientRead : eval flagged (.load .one (addConst (localVar "m") 32#64)) = some (.val (.word recipient)) := by
    apply FieldStores.Value.read flagged "m" (BitVec.ofNat 64 messageStart) (.copied 32 recipient)
    refine ⟨messageLocal, ?_, ?_⟩
    · rw [show flagged.memaddrs = source.memaddrs from rfl, environment.domain]
      exact MemoryRegion.word_mapped ⟨messageStart, 176⟩ region 32 (by change 32 + 8 ≤ 176; decide) (by decide)
    · exact (MessageField.scalar_other source messageStart 136 32 1#64 (by decide) (by decide) (by decide)).trans recipientCell
  have args : evalListHOLFinite flagged (h := fun address => Classical.propDecidable (flagged.memaddrs address))
      [localVar "aa", .load .one (addConst (localVar "m") 32#64), .const 1#64] = some (TableCall.values (cell plan .header 0) recipient 1#64) := by
    simp only [eval] at recipientRead
    simp only [evalListHOLFinite, evalListHOLExact, recipientRead]
    simp [evalHOLExact, localVar, toExact, aaLocal, flagged, MessageField.putState, TableCall.values]
  obtain ⟨paid, nextPlan, nextSlots, nextCursor, fits, clockEq, forward, budget, nextTable, nextReader, nextApart, countLow, countHigh, capacity, headerSame,
    localsSame, codesSame, nextEnvironment, protectedWords⟩ :=
    LiveTableSetter.normal_bound flagged called .account .storage plan reader slots readerSlots cursor floor readerFloor
      (environment.of_fields rfl rfl rfl) flaggedTable flaggedReader apart recipient 1#64 _ queryFits queryMapped args setRun
  have calledMessage : called.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))) := by rw [localsSame]; exact messageLocal
  have calledAA : called.locals.lookup (ofString "aa") = some (.val (.word (cell nextPlan .header 0))) := by rw [localsSame, headerSame]; exact aaLocal
  have calledAK : called.locals.lookup (ofString "ak") = some (.val (.word (cell reader .header 0))) := by rw [localsSame]; exact akLocal
  have gasBefore : (BitVec.ofNat 64 messageStart + 40#64).toNat < floor := by
    rw [MessageField.field_number messageStart 40 region (by decide)]
    omega
  have calledGas : called.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas :=
    (protectedWords _ gasBefore).trans ((MessageField.scalar_other source messageStart 136 40 1#64 (by decide) (by decide) (by decide)).trans gasCell)
  let ready := linkedState called messageStart (cell nextPlan .header 0) (cell reader .header 0)
  have links := links_execute called messageStart (cell nextPlan .header 0) (cell reader .header 0) region nextEnvironment.domain calledMessage calledAA calledAK
  have readyRun : evaluateHOLFiniteState ready messageSite = (some (.returned value), post) := links.symm.trans restRun
  have nextLater : ∀ pool, messageStart + 176 ≤ nextPlan.base pool := by intro pool; have lower := nextTable.lower pool; omega
  have pointers := linked_pointers called messageStart (cell nextPlan .header 0) (cell reader .header 0)
  refine ⟨paid, nextPlan, nextSlots, nextCursor, ready, fits, clockEq, forward, budget,
    linked_table called .account nextPlan nextSlots nextCursor floor messageStart _ _ nextTable region nextLater,
    linked_table called .storage reader readerSlots nextCursor readerFloor messageStart _ _ nextReader region readerLater,
    nextApart, countLow, countHigh, capacity, headerSame, localsSame, codesSame, nextEnvironment.of_fields rfl rfl rfl,
    (linked_gas called messageStart _ _).trans calledGas, pointers.1, pointers.2, readyRun, ?_⟩
  intro query earlier
  exact (linked_outside called messageStart _ _ query region (Or.inl earlier)).trans
    ((protectedWords query (by omega)).trans (MessageField.scalar_outside source messageStart 136 1#64 query region (by decide) (Or.inl earlier)))

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.final_set_normal
