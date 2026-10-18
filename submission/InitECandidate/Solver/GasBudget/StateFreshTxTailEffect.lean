import InitECandidate.Solver.GasBudget.StateFreshTxProgram
import InitECandidate.Solver.GasBudget.JournalStep
import InitECandidate.Solver.Input.GlobalAssignNormal

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def stepState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) (spec : Spec) :=
  let constructed := TableRuntime.callState source "t" spec.kind start spec.capacity
  {constructed with memory := StoreWord.put constructed.memory (MemoryRegion.address ⟨tx, 72⟩ spec.offset) (BitVec.ofNat 64 start)}

def walk (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) : List Spec → PanSemStateFiniteExact 64 Guest.HostMemory
  | [] => emptyLocalsHOLFinite (Input.putGlobal source "journal_n" 0#64)
  | spec :: rest => walk (stepState source start tx spec) (freshEnd spec.kind start spec.capacity) tx rest

theorem walk_clock (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :
    (walk source start tx specs).clock = source.clock - price specs := by
  induction specs generalizing source start with
  | nil => simp [walk, price, Input.putGlobal, emptyLocalsHOLFinite]
  | cons spec rest ih =>
    rw [walk, ih]
    change source.clock - spec.price - price rest = source.clock - (spec.price + price rest)
    omega

/-- The actual assigned-constructor/store tail has its exact summed clock
and full state effect. Every reached layout and call clock is derived; no
future allocation room, table result or successful helper trace is supplied. -/
theorem tail_effect (specs : List Spec) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) (old : BitVec 64)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (recordValid : MemoryRegion.Valid ⟨tx, 72⟩)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (ts : source.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 tx))))
    (t : source.locals.lookup (ofString "t") = some (.val (.word old)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (wellFormed : ∀ spec ∈ specs, spec.Valid) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (tailProgram specs) = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ price specs ≤ source.clock ∧ target = walk source start tx specs ∧
      cursor start specs ≤ 33806089496 ∧ cursor start specs % 8 = 0 ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor start specs)))) ∧
      WarmKeys.Environment target ∧ Journal.OtherGlobals source target := by
  induction specs generalizing source start old with
  | nil =>
    have safe : Input.LocalPrefix (ofString "setup") reset := .globalAssign _ _
    obtain ⟨middle, assigned, returnRun, saved⟩ := safe.normal_continue source target (.return (.const 0#64)) returned normal
    have same : middle = Input.putGlobal source "journal_n" 0#64 := Input.global_assign_none source middle "journal_n" _ _ rfl assigned
    subst middle
    have actual : evaluateHOLFiniteState (Input.putGlobal source "journal_n" 0#64) (.return (.const 0#64)) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite (Input.putGlobal source "journal_n" 0#64)) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    have returnedEq : returned = .val (.word 0#64) := by
      simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actual)
    have targetEq := congrArg Prod.snd (returnRun.symm.trans actual)
    change target = emptyLocalsHOLFinite (Input.putGlobal source "journal_n" 0#64) at targetEq
    subst target
    refine ⟨returnedEq, by simp [price], rfl, bounded, aligned, ?_, environment.of_fields rfl rfl rfl, ?_⟩
    · exact (Input.putGlobal.lookup_other source "journal_n" 0#64 (ofString "heap_ptr") (by decide)).trans heap
    · intro key heapOther different
      exact Input.putGlobal.lookup_other source "journal_n" 0#64 key different
  | cons spec rest ih =>
    have validSpec := wellFormed spec (by simp)
    have callSafe : Input.LocalPrefix (ofString "setup") spec.call :=
      .call (some (ofString "t")) _ _ (by intro name same; cases same; decide)
    obtain ⟨constructed, constructorRun, storeTailRun, saved⟩ := callSafe.normal_continue source target (.seq spec.store (tailProgram rest)) returned normal
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) spec.arguments =
        some (TableRuntime.values spec.kind spec.capacity) := by
      simp [Spec.arguments, TableRuntime.values, evalListHOLFinite, evalListHOLExact, evalHOLExact]
    obtain ⟨funded, valid, constructedEq⟩ := Journal.assigned_new_effect source constructed "t" old spec.kind start spec.capacity spec.bits environment lower bounded aligned rfl validSpec.1
      (Nat.pow_le_pow_right (by decide) validSpec.2.1) t newCode heap _ args constructorRun
    subst constructed
    let entered := TableRuntime.callState source "t" spec.kind start spec.capacity
    have tsEntered : entered.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 tx))) :=
      (HeapGlobals.update source (BitVec.ofNat 64 (freshEnd spec.kind start spec.capacity)) (ofString "ts") (by decide)).trans ts
    have tEntered : entered.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 start))) := bind_lookup_same _ _ _
    have tRead : eval entered (localVar "t") = some (.val (.word (BitVec.ofNat 64 start))) := by
      simp [eval, localVar, evalHOLExact, toExact, tEntered]
    have storeActual := Input.global_field_store entered "ts" ⟨tx, 72⟩ recordValid environment.domain spec.offset validSpec.2.2.2.1 validSpec.2.2.2.2 tsEntered
      (localVar "t") (BitVec.ofNat 64 start) tRead
    have storeSafe : Input.LocalPrefix (ofString "setup") spec.store := .store _ _
    obtain ⟨stored, storeRun, tailRun, storeSaved⟩ := storeSafe.normal_continue entered target (tailProgram rest) returned storeTailRun
    have storedEq := congrArg Prod.snd (storeRun.symm.trans storeActual)
    change stored = stepState source start tx spec at storedEq
    subst stored
    let next := stepState source start tx spec
    have nextBound : freshEnd spec.kind start spec.capacity ≤ 33806089496 := valid.upper .position
    have nextAligned : freshEnd spec.kind start spec.capacity % 8 = 0 := by
      have position := valid.aligned .position
      change ((fresh spec.kind start spec.capacity).base .position + 8 * spec.capacity) % 8 = 0
      rw [Nat.add_mod, position]
      omega
    have nextLower : 2701131776 ≤ freshEnd spec.kind start spec.capacity := by dsimp only [freshEnd]; omega
    have nextHeap : next.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (freshEnd spec.kind start spec.capacity)))) := by
      simp [next, stepState, TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have nextEnvironment : WarmKeys.Environment next := environment.of_fields rfl rfl rfl
    obtain ⟨returnedEq, restFits, targetEq, finalBound, finalAligned, finalHeap, finalEnvironment, finalGlobals⟩ :=
      ih (source := next) (start := freshEnd spec.kind start spec.capacity) (old := BitVec.ofNat 64 start) nextEnvironment nextLower nextBound nextAligned nextHeap tsEntered tEntered newCode
        (by intro next member; exact wellFormed next (by simp [member])) tailRun
    change price rest ≤ source.clock - spec.price at restFits
    refine ⟨returnedEq, ?_, targetEq, finalBound, finalAligned, finalHeap, finalEnvironment, ?_⟩
    · change spec.price + price rest ≤ source.clock
      change spec.price ≤ source.clock at funded
      omega
    · intro key heapOther different
      exact (finalGlobals key heapOther different).trans (HeapGlobals.update source (BitVec.ofNat 64 (freshEnd spec.kind start spec.capacity)) key heapOther)

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.walk_clock
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.tail_effect
