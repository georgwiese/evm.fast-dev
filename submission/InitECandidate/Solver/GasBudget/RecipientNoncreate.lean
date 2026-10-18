import InitECandidate.Solver.GasBudget.RecipientChoice
import InitECandidate.Solver.GasBudget.RecipientFinalSet
import InitECandidate.Solver.MutableTable.TableStateAlloc

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

def price (capacity population : Nat) : Nat :=
  Set.noGrowthPrice .account population + 2 +
    GrowRuntime.growthPotential .account (max capacity (4 * (population + 2))) - GrowRuntime.growthPotential .account capacity

theorem price_bound (paid capacity population nextCapacity nextPopulation : Nat)
    (budget : paid + GrowRuntime.growthPotential .account capacity ≤ Set.noGrowthPrice .account population + 2 + GrowRuntime.growthPotential .account nextCapacity)
    (count : nextPopulation ≤ population + 1) (high : nextCapacity ≤ max capacity (4 * (nextPopulation + 1))) :
    paid ≤ price capacity population := by
  have capacityBound : nextCapacity ≤ max capacity (4 * (population + 2)) := by omega
  have potential := GrowRuntime.potential_mono .account _ _ capacityBound
  unfold price
  omega

/-- The actual non-creation recipient phase, beginning at the real end of
key warming. Its empty-buffer reservation is justified by the reached
normal allocator, and the final real account insertion retains the other
table and root gas word through the process_message_call entry. -/
theorem noncreate_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (plan reader : Plan) (slots readerSlots : List Nat) (cursor floor readerFloor messageStart txStart : Nat)
    (recipient data length gas : BitVec 64) (environment : WarmKeys.Environment source)
    (table : TableState source .account plan slots cursor floor)
    (readerTable : TableState source .storage reader readerSlots cursor readerFloor)
    (apart : ∀ first second, plan.base first + size .account plan first ≤ reader.base second ∨ reader.base second + size .storage reader second ≤ plan.base first)
    (region : MemoryRegion.Valid ⟨messageStart, 176⟩) (before : messageStart + 176 ≤ floor)
    (readerLater : ∀ pool, messageStart + 176 ≤ reader.base pool)
    (record : TxData source.memory txStart messageStart recipient data length)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))))
    (txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 txStart))))
    (aaLocal : source.locals.lookup (ofString "aa") = some (.val (.word (cell plan .header 0))))
    (akLocal : source.locals.lookup (ofString "ak") = some (.val (.word (cell reader .header 0))))
    (gasCell : source.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas) (nonzero : recipient ≠ 0#64)
    (queryFits : recipient.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress recipient offset)))
    (normal : evaluateHOLFiniteState source WarmKeys.afterLoop = (some (.returned value), post)) :
    ∃ paid nextPlan nextSlots nextCursor ready finish,
      paid ≤ source.clock ∧ paid ≤ price plan.capacity slots.length ∧ ready.clock = source.clock - paid ∧ cursor + 8 ≤ nextCursor ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ Set.noGrowthPrice .account slots.length + 2 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState ready .account nextPlan nextSlots nextCursor floor ∧ TableState ready .storage reader readerSlots nextCursor readerFloor ∧
      (∀ first second, nextPlan.base first + size .account nextPlan first ≤ reader.base second ∨ reader.base second + size .storage reader second ≤ nextPlan.base first) ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧ nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      ready.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 messageStart))) ∧
      ready.locals.lookup (ofString "aa") = some (.val (.word (cell nextPlan .header 0))) ∧
      ready.locals.lookup (ofString "ak") = some (.val (.word (cell reader .header 0))) ∧
      ready.code = source.code ∧ WarmKeys.Environment ready ∧
      ready.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas ∧
      ready.memory (BitVec.ofNat 64 messageStart + 112#64) = .word (BitVec.ofNat 64 cursor) ∧
      ready.memory (BitVec.ofNat 64 messageStart + 120#64) = .word 0#64 ∧
      ready.memory (BitVec.ofNat 64 messageStart + 48#64) = source.memory (BitVec.ofNat 64 messageStart + 48#64) ∧
      ready.memory (BitVec.ofNat 64 messageStart + 152#64) = .word (cell nextPlan .header 0) ∧
      ready.memory (BitVec.ofNat 64 messageStart + 160#64) = .word (cell reader .header 0) ∧
      evaluateHOLFiniteState ready messageSite = (some (.returned value), finish) ∧ post = restore source "empty" finish ∧
      ∀ query : BitVec 64, query.toNat < messageStart → ready.memory query = source.memory query := by
  rw [empty_entry, StateSteps.next_sequence source source .skip _ (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _)] at normal
  obtain ⟨_, room, positive, finish, allocatedRun, restored⟩ := PersistentAlloc.call_normal_expected source post "empty" _ afterEmpty cursor 8 (cursor + 8)
    table.bounded (by decide) (Nat.le_refl _) (by omega) (by have aligned := table.aligned; omega) rfl environment.allocCode environment.trapCode table.heap value normal
  let allocated := PersistentAlloc.nextState source "empty" cursor (cursor + 8)
  have allocatedLocal (name : String) (other : ofString "empty" ≠ ofString name) : allocated.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    bind_lookup_other _ "empty" name _ other
  have allocatedMessage := (allocatedLocal "m" (by decide)).trans messageLocal
  have allocatedTx := (allocatedLocal "tx" (by decide)).trans txLocal
  have allocatedAA := (allocatedLocal "aa" (by decide)).trans aaLocal
  have allocatedAK := (allocatedLocal "ak" (by decide)).trans akLocal
  have emptyLocal : allocated.locals.lookup (ofString "empty") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
  have choice := noncreate_choice allocated messageStart txStart recipient data length (BitVec.ofNat 64 cursor) region record environment.domain allocatedMessage allocatedTx emptyLocal nonzero
  let chosen := resultState allocated (BitVec.ofNat 64 messageStart) recipient data length (BitVec.ofNat 64 cursor)
  have chosenRun : evaluateHOLFiniteState chosen afterChoice = (some (.returned value), finish) := choice.symm.trans allocatedRun
  have accountLater : ∀ pool, messageStart + 176 ≤ plan.base pool := by intro pool; have lower := table.lower pool; omega
  have chosenAccount := result_table allocated .account plan slots (cursor + 8) floor messageStart recipient data length (BitVec.ofNat 64 cursor)
    (table.after_alloc "empty" (cursor + 8) (by omega) room (by have aligned := table.aligned; omega)) region accountLater
  have chosenReader := result_table allocated .storage reader readerSlots (cursor + 8) readerFloor messageStart recipient data length (BitVec.ofNat 64 cursor)
    (readerTable.after_alloc "empty" (cursor + 8) (by omega) room (by have aligned := table.aligned; omega)) region readerLater
  have chosenGas : chosen.memory (BitVec.ofNat 64 messageStart + 40#64) = .word gas := (result_gas source.memory _ recipient data length _).trans gasCell
  obtain ⟨paid, nextPlan, nextSlots, nextCursor, ready, fits, clockEq, forward, budget, nextTable, nextReader, nextApart, countLow, countHigh, capacity,
    headSame, localsSame, codesSame, nextEnvironment, nextGas, pointerAA, pointerAK, readyRun, messageFrame, protectedWords⟩ :=
    final_set_normal chosen finish value plan reader slots readerSlots (cursor + 8) floor readerFloor messageStart recipient gas
      (environment.of_fields rfl rfl rfl) chosenAccount chosenReader apart region before readerLater allocatedMessage allocatedAA allocatedAK
      (result_recipient source.memory _ recipient data length _) chosenGas queryFits queryMapped chosenRun
  have totalBudget : paid + 1 + GrowRuntime.growthPotential .account plan.capacity ≤ Set.noGrowthPrice .account slots.length + 2 + GrowRuntime.growthPotential .account nextPlan.capacity := by omega
  refine ⟨paid + 1, nextPlan, nextSlots, nextCursor, ready, finish, ?_, price_bound _ _ _ _ _ totalBudget countHigh capacity, ?_, forward, totalBudget, nextTable, nextReader, nextApart,
    countLow, countHigh, capacity, ?_, ?_, ?_, codesSame, nextEnvironment, nextGas,
    (messageFrame 112 (by decide) (by decide) (by decide) (by decide)).trans (result_code source.memory _ recipient data length _),
    (messageFrame 120 (by decide) (by decide) (by decide) (by decide)).trans (result_length source.memory _ recipient data length _),
    (messageFrame 48 (by decide) (by decide) (by decide) (by decide)).trans (result_reservoir source.memory _ recipient data length _),
    pointerAA, pointerAK, readyRun, restored, ?_⟩
  · change paid ≤ source.clock - 1 at fits
    omega
  · change ready.clock = source.clock - 1 - paid at clockEq
    omega
  · rw [localsSame]; exact allocatedMessage
  · rw [localsSame, headSame]; exact allocatedAA
  · rw [localsSame]; exact allocatedAK
  · intro query earlier
    exact (protectedWords query earlier).trans (result_outside source.memory messageStart recipient data length _ query region (Or.inl earlier))

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.noncreate_normal
#print axioms InitECandidate.Solver.GasBudget.Recipient.price_bound
