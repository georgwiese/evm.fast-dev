import InitECandidate.Solver.GasBudget.JournalAppendDeleteRecordNormal
import InitECandidate.Solver.GasBudget.JournalAppendKeyFields

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def deleteSuffixPrice (kind : KeyHash.Kind) (population : Nat) : Nat := KeyHash.keySize kind + 2 + (Delete.modelPrice kind population + 1)

/-- Actual original jdel suffix after its executed presence/cap guards. The
key prefix and complete record/deletion suffix establish the next image with
the literal saved flag1, retaining all live tables and unused journal slots. -/
theorem delete_present_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (room : count < cap) (environment : WarmKeys.Environment source)
    (query oldValue : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (old : source.locals.lookup (ofString "old") = some (Get.pair 1#64 oldValue))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source deleteAfterGuard = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid : Nat) (next : TableFamily.Object),
      paid ≤ deleteSuffixPrice (objects writer).kind (objects writer).slots.length ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model post (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap (cursor + NaturalLayout.stride (objects writer).kind) ∧
      next.slots.length ≤ (objects writer).slots.length ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  rw [delete_key_shape] at normal
  obtain ⟨nextBound, keyFits, keyBound, region, keyPost, keyRun, keyFrame⟩ :=
    key_normal source post (objects writer).kind (objects writer).plan (objects writer).slots cursor (objects writer).floor (family.tables writer)
      environment query queryFits queryMapped tableLocal keyLocal deleteAfterCopy returned normal
  let copied := keyState source (objects writer).kind cursor query
  have copiedFamily := key_models source (objects writer).kind cursor query objects family region
  have copiedImage := key_image source (objects writer).kind cursor query objects base count entries image region (by have before := zone.earlier; omega)
  have copiedZone : Zone objects base cap (cursor + NaturalLayout.stride (objects writer).kind) := zone.advance (by omega)
  have copiedEnvironment : WarmKeys.Environment copied := environment.of_fields rfl rfl rfl
  have copiedT : copied.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) :=
    (key_local source (objects writer).kind cursor query "t" (by decide) (by decide)).trans tableLocal
  have copiedKey : copied.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (key_local source (objects writer).kind cursor query "key" (by decide) (by decide)).trans keyLocal
  have copiedOld : copied.locals.lookup (ofString "old") = some (Get.pair 1#64 oldValue) :=
    (key_local source (objects writer).kind cursor query "old" (by decide) (by decide)).trans old
  have copiedPointer : copied.locals.lookup (ofString "kc") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
  have copiedJournal : copied.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))) :=
    (key_globals source (objects writer).kind cursor query (ofString "journal") (by decide)).trans journal
  have copiedCounter : copied.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))) :=
    (key_globals source (objects writer).kind cursor query (ofString "journal_n") (by decide)).trans counter
  obtain ⟨copiedFits, copiedMapped⟩ := copied_key_geometry source (objects writer).kind cursor query region environment.domain
  obtain ⟨returnedEq, deletePaid, next, bounded, fits, finalClock, kind, plan, models, nextImage, nextZone, population,
    nextCounter, codes, nextEnvironment, globals⟩ :=
    delete_record_normal copied keyPost (cursor + NaturalLayout.stride (objects writer).kind) objects writer base cap count entries copiedFamily copiedImage copiedZone room copiedEnvironment
      query (BitVec.ofNat 64 cursor) oldValue queryFits queryMapped copiedFits copiedMapped copiedT copiedKey copiedPointer copiedOld copiedJournal copiedCounter deleteCode returned keyRun
  have finalFamily : TableFamily.Model post (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) := by
    rw [keyFrame]
    exact ⟨fun index => (models.tables index).of_fields rfl rfl rfl rfl, models.apart⟩
  have finalImage : Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) := by
    rw [keyFrame]
    exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalCounter : post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by rw [keyFrame]; exact nextCounter
  have finalCodes : post.code = source.code := by rw [keyFrame]; exact codes
  have finalEnvironment : WarmKeys.Environment post := by rw [keyFrame]; exact nextEnvironment.of_fields rfl rfl rfl
  have postClock : post.clock = keyPost.clock := by rw [keyFrame]; rfl
  have copiedClock : copied.clock = source.clock - keyPrice (objects writer).kind cursor query := key_clock source _ cursor query
  rw [copiedClock] at fits finalClock
  refine ⟨returnedEq, keyPrice (objects writer).kind cursor query + deletePaid, next, ?_, by omega, ?_, kind, plan, finalFamily, finalImage,
    nextZone, population, finalCounter, finalCodes, finalEnvironment, ?_⟩
  · dsimp only [deleteSuffixPrice]
    omega
  · rw [postClock, finalClock]
    omega
  · intro key heap different
    have finalGlobal : post.globals.lookup key = keyPost.globals.lookup key := by rw [keyFrame]; rfl
    exact finalGlobal.trans ((globals key heap different).trans (key_globals source (objects writer).kind cursor query key heap))

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_present_normal
