import InitECandidate.Solver.GasBudget.JournalProtectedFrame
import InitECandidate.Solver.GasBudget.JournalAppendDeleteTailValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete original post-copy jdel suffix with its literal saved flag1,
actual record stores, counter increment, deletion and zero return. -/
theorem delete_record_normal_values {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (room : count < cap) (environment : WarmKeys.Environment source)
    (query copiedKey oldValue : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (copiedFits : copiedKey.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (copiedMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress copiedKey offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (copyLocal : source.locals.lookup (ofString "kc") = some (.val (.word copiedKey)))
    (old : source.locals.lookup (ofString "old") = some (Get.pair 1#64 oldValue))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source deleteAfterCopy = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid : Nat) (next : TableFamily.Object),
      paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model post cursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, copiedKey, 1#64, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap cursor ∧ next.slots.length ≤ (objects writer).slots.length ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post ∧ ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property := by
  let newRecord : Entry ι := ⟨writer, copiedKey, 1#64, oldValue⟩
  have execute := record_execute source objects base cap count cursor newRecord 1#64 true zone room environment.domain journal counter tableLocal copyLocal old rfl
  change evaluateHOLFiniteState source deleteAfterCopy = _ at execute
  rw [execute] at normal
  let entry := recorded source objects base count newRecord
  let finish := (evaluateHOLFiniteState entry (afterStores deleteAfterCopy)).2
  have result := congrArg Prod.fst normal
  change (evaluateHOLFiniteState entry (afterStores deleteAfterCopy)).1 = some (.returned returned) at result
  have tailRun : evaluateHOLFiniteState entry (afterStores deleteAfterCopy) = (some (.returned returned), finish) := Prod.ext result rfl
  have postEq := congrArg Prod.snd normal
  change restore source "r" finish = post at postEq
  have entryFamily := recorded_models source objects base cap count cursor newRecord family zone room
  have entryEffects := recorded_protected source objects base cap count cursor newRecord family zone room property values
  have entryImage := recorded_image source objects base cap count cursor newRecord entries image zone room environment.domain copiedFits copiedMapped
  have t : entry.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) :=
    (bind_lookup_other _ "r" "t" _ (by decide)).trans tableLocal
  have key : entry.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (bind_lookup_other _ "r" "key" _ (by decide)).trans keyLocal
  obtain ⟨returnedEq, paid, next, bounded, fits, clock, kind, plan, models, nextImage, nextZone, population, nextCounter, codes, nextEnvironment, globals, persistent, nextValues⟩ :=
    delete_tail_normal_values entry finish cursor objects writer base cap count (Function.update entries count newRecord) entryFamily entryImage zone
      (environment.of_fields rfl rfl rfl) query property entryEffects.2 queryFits queryMapped t key counter deleteCode returned tailRun
  have frame := entryEffects.1.trans (ProtectedFrame.of_persistent base cap cursor objects (Function.update objects writer next) entry finish persistent) (Nat.le_refl _)
  subst post
  have finalFamily : TableFamily.Model (restore source "r" finish) cursor (Function.update objects writer next) :=
    ⟨fun table => (models.tables table).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image (restore source "r" finish) (Function.update objects writer next) base (count + 1) (Function.update entries count newRecord) :=
    nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  exact ⟨returnedEq, paid, next, bounded, fits, clock, kind, plan, finalFamily, finalImage, nextZone, population, nextCounter,
    codes, nextEnvironment.of_fields rfl rfl rfl, globals,⟨frame.words⟩,nextValues⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_record_normal_values
