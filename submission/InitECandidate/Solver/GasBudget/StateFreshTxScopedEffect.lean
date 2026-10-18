import InitECandidate.Solver.GasBudget.StateFreshTxTailEffect

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def scopedState (spec : Spec) (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :=
  restore source "t" (walk (stepState source start tx spec) (freshEnd spec.kind start spec.capacity) tx specs)

/-- A scoped constructor, its pointer store, and the assigned-constructor
tail. Allocation guards and clock funding come from the normal execution
of the original suffix. -/
theorem scoped_effect (spec : Spec) (specs : List Spec) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start)
    (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (recordValid : MemoryRegion.Valid ⟨tx, 72⟩)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (ts : source.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 tx))))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (validSpec : spec.Valid) (wellFormed : ∀ next ∈ specs, next.Valid)
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "htab_new") spec.arguments (.seq spec.store (tailProgram specs))) = (some (.returned returned), target)) :
    returned = .val (.word 0#64) ∧ price (spec :: specs) ≤ source.clock ∧
      target = scopedState spec specs source start tx ∧ cursor start (spec :: specs) ≤ 33806089496 ∧
      cursor start (spec :: specs) % 8 = 0 ∧
      target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor start (spec :: specs))))) ∧
      WarmKeys.Environment target ∧ Journal.OtherGlobals source target := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) spec.arguments =
      some (TableRuntime.values spec.kind spec.capacity) := by
    simp [Spec.arguments, TableRuntime.values, evalListHOLFinite, evalListHOLExact, evalHOLExact]
  obtain ⟨positive, multiple, keySmall, wordSmall, capSmall⟩ := Journal.new_capacity_bounds spec.kind spec.capacity spec.bits rfl validSpec.1 (Nat.pow_le_pow_right (by decide) validSpec.2.1)
  have valid := TableRuntime.normal_call_layout source target spec.kind start spec.capacity "t" spec.arguments (.seq spec.store (tailProgram specs))
    positive lower bounded aligned keySmall wordSmall capSmall multiple environment.domain args newCode heap environment.allocCode environment.trapCode environment.zeroCode returned normal
  obtain ⟨funded, inner, continuationRun, restored⟩ := TableRuntime.call_normal source target spec.kind start spec.capacity "t" spec.arguments (.seq spec.store (tailProgram specs))
    valid environment.domain (Or.inr multiple) args newCode heap environment.allocCode environment.zeroCode returned normal
  let entered := TableRuntime.callState source "t" spec.kind start spec.capacity
  have tsEntered : entered.globals.lookup (ofString "ts") = some (.val (.word (BitVec.ofNat 64 tx))) :=
    (HeapGlobals.update source (BitVec.ofNat 64 (freshEnd spec.kind start spec.capacity)) (ofString "ts") (by decide)).trans ts
  have tEntered : entered.locals.lookup (ofString "t") = some (.val (.word (BitVec.ofNat 64 start))) := bind_lookup_same _ _ _
  have tRead : eval entered (localVar "t") = some (.val (.word (BitVec.ofNat 64 start))) := by
    simp [eval, localVar, evalHOLExact, toExact, tEntered]
  have storeActual := Input.global_field_store entered "ts" ⟨tx, 72⟩ recordValid environment.domain spec.offset validSpec.2.2.2.1 validSpec.2.2.2.2 tsEntered
    (localVar "t") (BitVec.ofNat 64 start) tRead
  have storeSafe : Input.LocalPrefix (ofString "setup") spec.store := .store _ _
  obtain ⟨stored, storeRun, tailRun, saved⟩ := storeSafe.normal_continue entered inner (tailProgram specs) returned continuationRun
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
  obtain ⟨returnedEq, restFits, innerEq, finalBound, finalAligned, finalHeap, finalEnvironment, finalGlobals⟩ :=
    tail_effect specs next inner (freshEnd spec.kind start spec.capacity) tx (BitVec.ofNat 64 start)
      (environment.of_fields rfl rfl rfl) nextLower nextBound nextAligned recordValid nextHeap tsEntered tEntered newCode
      wellFormed returned tailRun
  refine ⟨returnedEq, ?_, restored.trans (congrArg (restore source "t") innerEq), finalBound, finalAligned, ?_, ?_, ?_⟩
  · change price specs ≤ source.clock - spec.price at restFits
    change spec.price ≤ source.clock at funded
    change spec.price + price specs ≤ source.clock
    omega
  · rw [restored]
    exact finalHeap
  · rw [restored]
    exact finalEnvironment.of_fields rfl rfl rfl
  · intro key heapOther different
    rw [restored]
    exact (finalGlobals key heapOther different).trans (HeapGlobals.update source (BitVec.ofNat 64 (freshEnd spec.kind start spec.capacity)) key heapOther)

theorem scoped_clock (spec : Spec) (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :
    (scopedState spec specs source start tx).clock = source.clock - price (spec :: specs) := by
  change (walk (stepState source start tx spec) (freshEnd spec.kind start spec.capacity) tx specs).clock = _
  rw [walk_clock]
  change source.clock - spec.price - price specs = source.clock - (spec.price + price specs)
  omega

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.scoped_effect
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.scoped_clock
