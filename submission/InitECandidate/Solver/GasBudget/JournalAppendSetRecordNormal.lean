import InitECandidate.Solver.GasBudget.JournalAppendRecordEntry

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Full actual post-copy jset suffix: the record declaration, four writes,
counter increment, final mutation and zero return. The next journal image
and complete reservation follow from physical input ownership. -/
theorem set_record_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (room : count < cap) (environment : WarmKeys.Environment source)
    (query value copiedKey oldFlag oldValue : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (copiedFits : copiedKey.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (copiedMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress copiedKey offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (copyLocal : source.locals.lookup (ofString "kc") = some (.val (.word copiedKey)))
    (old : source.locals.lookup (ofString "old") = some (Get.pair oldFlag oldValue))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source setAfterCopy = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, copiedKey, oldFlag, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  let newRecord : Entry ι := ⟨writer, copiedKey, oldFlag, oldValue⟩
  have execute := record_execute source objects base cap count cursor newRecord oldFlag false zone room environment.domain journal counter tableLocal copyLocal old rfl
  change evaluateHOLFiniteState source setAfterCopy = _ at execute
  rw [execute] at normal
  let entry := recorded source objects base count newRecord
  let finish := (evaluateHOLFiniteState entry (afterStores setAfterCopy)).2
  have result := congrArg Prod.fst normal
  change (evaluateHOLFiniteState entry (afterStores setAfterCopy)).1 = some (.returned returned) at result
  have tailRun : evaluateHOLFiniteState entry (afterStores setAfterCopy) = (some (.returned returned), finish) := Prod.ext result rfl
  have postEq := congrArg Prod.snd normal
  change restore source "r" finish = post at postEq
  have entryFamily := recorded_models source objects base cap count cursor newRecord family zone room
  have entryImage := recorded_image source objects base cap count cursor newRecord entries image zone room environment.domain copiedFits copiedMapped
  have t : entry.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) :=
    (bind_lookup_other _ "r" "t" _ (by decide)).trans tableLocal
  have key : entry.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other _ "r" "key" _ (by decide)).trans keyLocal
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) :=
    (bind_lookup_other _ "r" "value" _ (by decide)).trans valueLocal
  obtain ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, kind, models, nextImage, nextZone, bounded, population, nextCounter, codes, nextEnvironment, globals⟩ :=
    set_tail_normal entry finish cursor objects writer base cap count (Function.update entries count newRecord) entryFamily entryImage zone room
      (environment.of_fields rfl rfl rfl) query value queryFits queryMapped t key v counter returned tailRun
  subst post
  have finalFamily : TableFamily.Model (restore source "r" finish) nextCursor (Function.update objects writer next) :=
    ⟨fun table => (models.tables table).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image (restore source "r" finish) (Function.update objects writer next) base (count + 1) (Function.update entries count newRecord) :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  exact ⟨returnedEq, paid, nextCursor, next, fits, clock, forward, kind, finalFamily, finalImage, nextZone, bounded, population, nextCounter,
    codes, nextEnvironment.of_fields rfl rfl rfl, globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_record_normal
