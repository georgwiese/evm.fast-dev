import InitECandidate.Solver.GasBudget.JournalInitProgram

namespace InitECandidate.Solver.GasBudget.Journal.Initialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original initialization suffix derives the reached16MiB reservation,
one allocation clock, three actual global resets and exact full state.
Old cap/counter/transaction bindings need no supplied validity/value oracle. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (journalOld : BitVec 64)
    (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word journalOld)))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source selected = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ cursor + bytes ≤ 33806089496 ∧ 1 ≤ source.clock ∧
      target = emptyLocalsHOLFinite (initialized source cursor) := by
  rw [actual_site, program] at run
  have capSafe : Input.LocalPrefix (ofString "setup") setCap := .globalAssign _ _
  obtain ⟨withCap, capRun, tailRun, saved⟩ := capSafe.normal_continue source target (.seq allocate afterAllocation) returned run
  have capEq : withCap = capState source := Input.global_assign_none source withCap "journal_cap" _ _ rfl capRun
  subst withCap
  have allocationSafe : Input.LocalPrefix (ofString "setup") allocate := .globalCall _ _ _
  obtain ⟨allocatedPost, allocationRun, afterAllocationRun, allocationSaved⟩ := allocationSafe.normal_continue (capState source) target afterAllocation returned tailRun
  have cap : (capState source).globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 capacity))) := Input.putGlobal.lookup_same source "journal_cap" _
  have args : evalListHOLFinite (capState source) (h := fun address => Classical.propDecidable ((capState source).memaddrs address)) allocationArguments =
      some (PersistentAlloc.values (BitVec.ofNat 64 bytes)) := by
    simp [allocationArguments, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, cap,
      valueIsWord, valueWord, panOpHOL, PersistentAlloc.values, bytes, capacity]
  have capJournal : (capState source).globals.lookup (ofString "journal") = some (.val (.word journalOld)) :=
    (Input.putGlobal.lookup_other source "journal_cap" _ (ofString "journal") (by decide)).trans journal
  have capHeap : (capState source).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))) :=
    (Input.putGlobal.lookup_other source "journal_cap" _ (ofString "heap_ptr") (by decide)).trans heap
  have nextAligned : (cursor + bytes) % 8 = 0 := by rw [Nat.add_mod, aligned, show bytes % 8 = 0 from by decide]
  obtain ⟨room, nextBound, positive, allocatedEq⟩ := PersistentAlloc.global_call_normal_expected (capState source) allocatedPost "journal" journalOld cursor bytes (cursor + bytes)
    bounded (by decide) (Nat.le_refl _) (by omega) nextAligned capJournal allocationArguments args allocCode trapCode capHeap allocationRun
  change allocatedPost = allocatedState source cursor at allocatedEq
  subst allocatedPost
  rw [afterAllocation] at afterAllocationRun
  have counterSafe : Input.LocalPrefix (ofString "setup") resetCounter := .globalAssign _ _
  obtain ⟨withCounter, counterRun, transactionRun, counterSaved⟩ := counterSafe.normal_continue (allocatedState source cursor) target
    (.seq resetTransaction (.return (.const 0#64))) returned afterAllocationRun
  have counterEq : withCounter = counterState source cursor := Input.global_assign_none (allocatedState source cursor) withCounter "journal_n" _ _ rfl counterRun
  subst withCounter
  have transactionSafe : Input.LocalPrefix (ofString "setup") resetTransaction := .globalAssign _ _
  obtain ⟨finished, transactionStep, returnRun, transactionSaved⟩ := transactionSafe.normal_continue (counterState source cursor) target (.return (.const 0#64)) returned transactionRun
  have finishedEq : finished = initialized source cursor := Input.global_assign_none (counterState source cursor) finished "ts" _ _ rfl transactionStep
  subst finished
  have actualReturn : evaluateHOLFiniteState (initialized source cursor) (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite (initialized source cursor)) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have returnedEq : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actualReturn)
  exact ⟨returnedEq, room, positive, congrArg Prod.snd (returnRun.symm.trans actualReturn)⟩

end InitECandidate.Solver.GasBudget.Journal.Initialization

#print axioms InitECandidate.Solver.GasBudget.Journal.Initialization.normal
