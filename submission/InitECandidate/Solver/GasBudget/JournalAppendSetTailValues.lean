import InitECandidate.Solver.GasBudget.JournalAppendCounter
import InitECandidate.Solver.GasBudget.JournalZoneSetValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- The real original append tail increments journal_n, performs its actual
setter with the original key, then returns zero. It retains all live record
images and unused journal slots across any reached table growth. -/
theorem set_tail_normal_values {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base (count + 1) entries)
    (zone : Zone objects base cap cursor) (room : count < cap) (environment : WarmKeys.Environment source)
    (query value : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer value)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterStores setAfterCopy) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) entries ∧ Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source post ∧ TableFamily.ValuesHave post (Function.update objects writer next) property := by
  let entry := Input.putGlobal source "journal_n" (BitVec.ofNat 64 count + 1#64)
  have incrementRun := increment_execute source (BitVec.ofNat 64 count) counter
  rw [set_tail_shape, StateSteps.next_sequence source entry _ _ incrementRun (Nat.le_refl _)] at normal
  have safe : Input.LocalPrefix (ofString "value") mutateSet := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨called, mutationRun, returnRun, saved⟩ := safe.normal_continue entry post (.return (.const 0#64)) returned normal
  have actualReturn : evaluateHOLFiniteState called (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite called) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
  have returnedEq : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actualReturn)
  have postEq := congrArg Prod.snd (returnRun.symm.trans actualReturn)
  change post = emptyLocalsHOLFinite called at postEq
  have entryFamily := increment_models source cursor objects family (BitVec.ofNat 64 count)
  have entryImage := increment_image source objects base (count + 1) entries image (BitVec.ofNat 64 count)
  have args : evalListHOLFinite entry (h := fun address => Classical.propDecidable (entry.memaddrs address)) [localVar "t", localVar "key", localVar "value"] =
      some (TableCall.values (objects writer).pointer query value) := by
    have t : entry.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) := tableLocal
    have key : entry.locals.lookup (ofString "key") = some (.val (.word query)) := keyLocal
    have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := valueLocal
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, t, key, v, TableCall.values]
  obtain ⟨paid, nextCursor, next, fits, clock, forward, kind, models, nextImage, nextZone, bounded, population, locals, codes, nextEnvironment, globals, _floorFrame, persistent, nextValues⟩ :=
    set_zone_normal_values entry called cursor objects writer base cap (count + 1) entries entryFamily entryImage zone (by omega)
      (environment.of_fields rfl rfl rfl) query value property values owned queryFits queryMapped _ args mutationRun
  have entryCounter : entry.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by
    change (Input.putGlobal source "journal_n" (BitVec.ofNat 64 count + 1#64)).globals.lookup _ = _
    rw [Input.putGlobal.lookup_same]
    simp only [BitVec.ofNat_add]
  have calledCounter := (globals (ofString "journal_n") (by decide)).trans entryCounter
  subst post
  have finalFamily : TableFamily.Model (emptyLocalsHOLFinite called) nextCursor (Function.update objects writer next) :=
    ⟨fun table => (models.tables table).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image (emptyLocalsHOLFinite called) (Function.update objects writer next) base (count + 1) entries :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  refine ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, kind, finalFamily, finalImage, nextZone, bounded, population, calledCounter,
    codes, nextEnvironment.of_fields rfl rfl rfl, ?_,⟨persistent.words⟩,nextValues⟩
  intro key heap different
  exact (globals key heap).trans (Input.putGlobal.lookup_other source "journal_n" _ key different)

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_tail_normal_values
