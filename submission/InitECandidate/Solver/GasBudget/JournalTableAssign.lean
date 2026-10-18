import InitECandidate.Solver.GasBudget.JournalTableNew
import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Original constructor assignment to an existing local. It derives the
same canonical result state as the scoped constructor entry, including all
six reached allocations, clear, header words and caller clock. -/
theorem assigned_new_effect (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (old : BitVec 64) (kind : KeyHash.Kind) (start capacity bits : Nat)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start)
    (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (power : capacity = 2 ^ bits) (minimum : 3 ≤ bits) (capBound : capacity ≤ 2 ^ 32)
    (present : source.locals.lookup (ofString name) = some (.val (.word old)))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableRuntime.values kind capacity))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local, ofString name), none)) (ofString "htab_new") arguments) = (none, target)) :
    TableRuntime.price capacity + 1 ≤ source.clock ∧ Valid kind (fresh kind start capacity) ∧
      target = TableRuntime.callState source name kind start capacity := by
  obtain ⟨positiveCapacity, multiple, keySmall, wordSmall, capSmall⟩ := new_capacity_bounds kind capacity bits power minimum capBound
  obtain ⟨callee, called, keyLocal, capLocal⟩ := TableRuntime.environment source.code.lookup kind capacity newCode
  obtain ⟨positive, bodyTarget, returned, bodyRun⟩ := Input.CallNormal.assigned_callee_return source target (some (.local, ofString name)) (ofString "htab_new") arguments _ TableNew.body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have valid := TableRuntime.normal_layout entry bodyTarget kind start capacity positiveCapacity lower bounded aligned keySmall wordSmall capSmall multiple environment.domain keyLocal capLocal heap
    environment.allocCode environment.trapCode environment.zeroCode returned bodyRun
  obtain ⟨bodyFunded, returnedEq, frame⟩ := TableRuntime.body_normal entry bodyTarget kind start capacity valid environment.domain (Or.inr multiple) keyLocal capLocal heap environment.allocCode environment.zeroCode returned bodyRun
  rw [returnedEq] at bodyRun
  have funded : TableRuntime.price capacity + 1 ≤ source.clock := by
    change TableRuntime.price capacity ≤ source.clock - 1 at bodyFunded
    omega
  have validDestination : isValidValueHOLFinite source .local (ofString name) (.val (.word (BitVec.ofNat 64 start))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, present, shapeOfHOLExact, shapeEqHOL]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .local (ofString name) none (ofString "htab_new") arguments _ TableNew.body callee .one
    (.val (.word (BitVec.ofNat 64 start))) bodyTarget args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
    (by simpa only [isValidValueHOLFinite_eq] using validDestination)
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  change {bodyTarget with locals := source.locals} = {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
    memory := TableRuntime.resultMemory source.memory source.be kind start capacity
    clock := source.clock - 1 - TableRuntime.price capacity} at callerFrame
  have subtract : source.clock - 1 - TableRuntime.price capacity = source.clock - (TableRuntime.price capacity + 1) := by omega
  rw [subtract] at callerFrame
  rw [callerFrame] at actual
  have same := congrArg Prod.snd (normal.symm.trans actual)
  exact ⟨funded, valid, same⟩

/-- Actual reused-local constructor extends the complete live identity
family and journal ownership, with no future-room or entry-clock premise. -/
theorem assigned_new_normal {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start capacity bits : Nat) (kind : KeyHash.Kind) (objects : ι → TableFamily.Object)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source start objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap start) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (power : capacity = 2 ^ bits) (minimum : 3 ≤ bits) (capBound : capacity ≤ 2 ^ 32)
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (name : String) (old : BitVec 64) (present : source.locals.lookup (ofString name) = some (.val (.word old)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableRuntime.values kind capacity))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local, ofString name), none)) (ofString "htab_new") arguments) = (none, target)) :
    TableRuntime.price capacity + 1 ≤ source.clock ∧ target = TableRuntime.callState source name kind start capacity ∧
      TableFamily.Model target (freshEnd kind start capacity) (TableFamily.extend objects (newObject kind start capacity)) ∧
      Image target (TableFamily.extend objects (newObject kind start capacity)) base count (fun index => (entries index).lift) ∧
      Zone (TableFamily.extend objects (newObject kind start capacity)) base cap (freshEnd kind start capacity) ∧
      WarmKeys.Environment target ∧ HeapGlobals source target := by
  obtain ⟨funded, valid, same⟩ := assigned_new_effect source target name old kind start capacity bits environment lower bounded aligned power minimum capBound present newCode heap arguments args normal
  have multiple := (new_capacity_bounds kind capacity bits power minimum capBound).2.1
  subst target
  exact ⟨funded, rfl, new_models source name start capacity bits kind objects base cap count entries family image zone countBound environment bounded power (by omega) multiple valid⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.assigned_new_effect
#print axioms InitECandidate.Solver.GasBudget.Journal.assigned_new_normal
