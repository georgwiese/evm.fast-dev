import InitECandidate.Solver.GasBudget.StateFreshTxScopedEffect
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def allocatedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) :=
  Input.putGlobal {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (start + 72))))
    clock := source.clock - 1} "ts" (BitVec.ofNat 64 start)

def blockStateStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (bs : BitVec 64) :=
  let allocated := allocatedState source start
  {allocated with memory := StoreWord.put allocated.memory (MemoryRegion.address ⟨start, 72⟩ 0) bs}

def resultState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (bs : BitVec 64) :=
  scopedState first rest (blockStateStored source start bs) (start + 72) start

/-- Complete actual original state_fresh_tx. Its record reservation, eight
constructors, nine record stores and counter reset are retained unchanged.
The 81 source clocks and 17176-byte reservation are derived from the normal
execution; source clocks do not account for straight-line target work. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (oldTs bs : BitVec 64)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start)
    (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (ts : source.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (blockState : source.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ 81 ≤ source.clock ∧ target = resultState source start bs ∧
      target.clock = source.clock - 81 ∧ start + 17176 ≤ 33806089496 ∧ (start + 17176) % 8 = 0 ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 17176)))) ∧
      target.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 start))) ∧
      WarmKeys.Environment target ∧
      (∀ key : MlS, key ≠ ofString "heap_ptr" → key ≠ ofString "journal_n" → key ≠ ofString "ts" →
        target.globals.lookup key = source.globals.lookup key) := by
  rw [body_shape, program] at normal
  have allocationSafe : Input.LocalPrefix (ofString "setup") allocate := .globalCall _ _ _
  obtain ⟨allocated, allocationRun, afterRun, saved⟩ := allocationSafe.normal_continue source target afterAllocation returned normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const 72#64] =
      some (PersistentAlloc.values 72#64) := by rfl
  have nextAligned : (start + 72) % 8 = 0 := by omega
  obtain ⟨room, nextBound, positive, allocatedEq⟩ := PersistentAlloc.global_call_normal_expected source allocated "ts" oldTs start 72 (start + 72)
    bounded (by decide) (Nat.le_refl _) (by omega) nextAligned ts [.const 72#64] args environment.allocCode environment.trapCode heap allocationRun
  change allocated = allocatedState source start at allocatedEq
  subst allocated
  have recordValid : MemoryRegion.Valid ⟨start, 72⟩ := ⟨lower, room, aligned⟩
  have allocatedTs : (allocatedState source start).globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 start))) :=
    Input.putGlobal.lookup_same _ _ _
  have allocatedBs : (allocatedState source start).globals.lookup (ofString "bs") = some (.val (.word bs)) := by
    exact (Input.putGlobal.lookup_other _ "ts" _ (ofString "bs") (by decide)).trans
      ((HeapGlobals.update source _ (ofString "bs") (by decide)).trans blockState)
  have bsRead : eval (allocatedState source start) (.var .global (ofString "bs")) = some (.val (.word bs)) := by
    simp [eval, evalHOLExact, allocatedBs]
  have storeActual := Input.global_field_store (allocatedState source start) "ts" ⟨start, 72⟩ recordValid environment.domain 0
    (by change 0 + 8 ≤ 72; decide) (by decide) allocatedTs (.var .global (ofString "bs")) bs bsRead
  have storeSafe : Input.LocalPrefix (ofString "setup") storeBlockState := .store _ _
  obtain ⟨stored, storeRun, scopedRun, storeSaved⟩ := storeSafe.normal_continue (allocatedState source start) target afterBlockState returned afterRun
  have storedEq := congrArg Prod.snd (storeRun.symm.trans storeActual)
  change stored = blockStateStored source start bs at storedEq
  subst stored
  let entered := blockStateStored source start bs
  have enteredHeap : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (start + 72)))) := by
    have different : ofString "ts" ≠ ofString "heap_ptr" := by decide
    simp [entered, blockStateStored, allocatedState, Input.putGlobal, HolFiniteMapExact.update, FUPDATE, different]
  have enteredEnvironment : WarmKeys.Environment entered := environment.of_fields rfl rfl rfl
  obtain ⟨returnedEq, funded, targetEq, finalBound, finalAligned, finalHeap, finalEnvironment, finalGlobals⟩ :=
    scoped_effect first rest entered target (start + 72) start enteredEnvironment (by omega) nextBound nextAligned recordValid enteredHeap allocatedTs newCode (specs_valid first (by simp)) (by intro spec member; exact specs_valid spec (List.mem_cons_of_mem first member)) returned scopedRun
  rw [cursor_all] at finalBound finalAligned finalHeap
  have priceValue : price (first :: rest) = 80 := by have := price_all; omega
  change price (first :: rest) ≤ source.clock - 1 at funded
  rw [priceValue] at funded
  refine ⟨returnedEq, by omega, targetEq, ?_, finalBound, finalAligned, finalHeap,
    (finalGlobals (ofString "ts") (by decide) (by decide)).trans allocatedTs, finalEnvironment, ?_⟩
  · rw [targetEq, scoped_clock]
    change source.clock - 1 - price (first :: rest) = source.clock - 81
    rw [priceValue]
    omega
  · intro key heapOther counterOther tsOther
    exact (finalGlobals key heapOther counterOther).trans
      ((Input.putGlobal.lookup_other _ "ts" _ key tsOther).trans (HeapGlobals.update source _ key heapOther))

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.body_normal
