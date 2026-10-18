import InitECandidate.Solver.GasBudget.JournalAppendCounter
import InitECandidate.Solver.GasBudget.JournalZoneDelete

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Original post-store jdel tail increments the counter, deletes with the
original query and returns zero. Every live/unused journal slot survives. -/
theorem delete_tail_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base (count + 1) entries)
    (zone : Zone objects base cap cursor) (environment : WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterStores deleteAfterCopy) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid : Nat) (next : TableFamily.Object),
      paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model post cursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) entries ∧ Zone (Function.update objects writer next) base cap cursor ∧
      next.slots.length ≤ (objects writer).slots.length ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  let entry := Input.putGlobal source "journal_n" (BitVec.ofNat 64 count + 1#64)
  have incrementRun := increment_execute source (BitVec.ofNat 64 count) counter
  rw [delete_tail_shape, StateSteps.next_sequence source entry _ _ incrementRun (Nat.le_refl _)] at normal
  have safe : Input.LocalPrefix (ofString "key") mutateDelete := .call none _ _ (by intro name impossible; cases impossible)
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
  have args : evalListHOLFinite entry (h := fun address => Classical.propDecidable (entry.memaddrs address)) [localVar "t", localVar "key"] =
      some [.val (.word (objects writer).pointer), .val (.word query)] := by
    have t : entry.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) := tableLocal
    have key : entry.locals.lookup (ofString "key") = some (.val (.word query)) := keyLocal
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, t, key]
  obtain ⟨paid, next, bounded, fits, clock, kind, plan, models, nextImage, nextZone, population, locals, globalEq, codes, nextEnvironment⟩ :=
    delete_zone_normal entry called cursor objects writer base cap (count + 1) entries entryFamily entryImage zone
      (environment.of_fields rfl rfl rfl) query queryFits queryMapped deleteCode _ args mutationRun
  have entryCounter : entry.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by
    change (Input.putGlobal source "journal_n" (BitVec.ofNat 64 count + 1#64)).globals.lookup _ = _
    rw [Input.putGlobal.lookup_same]
    simp only [BitVec.ofNat_add]
  have calledCounter : called.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by rw [globalEq]; exact entryCounter
  subst post
  have finalFamily : TableFamily.Model (emptyLocalsHOLFinite called) cursor (Function.update objects writer next) :=
    ⟨fun table => (models.tables table).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image (emptyLocalsHOLFinite called) (Function.update objects writer next) base (count + 1) entries :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  refine ⟨returnedEq, paid, next, bounded, fits, clock, kind, plan, finalFamily, finalImage, nextZone, population, calledCounter,
    codes, nextEnvironment.of_fields rfl rfl rfl, ?_⟩
  intro key heap different
  change called.globals.lookup key = source.globals.lookup key
  rw [globalEq]
  exact Input.putGlobal.lookup_other source "journal_n" _ key different

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_tail_normal
