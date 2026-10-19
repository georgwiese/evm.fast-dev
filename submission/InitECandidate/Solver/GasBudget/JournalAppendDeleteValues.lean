import InitECandidate.Solver.GasBudget.JournalAppendDeletePresentValues
import InitECandidate.Solver.GasBudget.JournalDeleteGuardValues
import InitECandidate.Solver.GasBudget.JournalEntryValues
import InitECandidate.Solver.GasBudget.JournalDeleteDefs

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete original jdel body. Its actual getter either yields an absent
key and a read-only return, or reaches the real guard/append/deletion path.
All clocks and physical postconditions follow from that normal execution. -/
theorem delete_body_normal_values {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (query : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source deleteBody = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧
      ((∃ paid, 1 ≤ paid ∧ paid ≤ Get.bodyPrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧
        emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - paid}) ∨
      (count < cap ∧ ∃ (paid : Nat) (next : TableFamily.Object) (oldValue : BitVec 64),
        1 ≤ paid ∧ paid ≤ deletePrice (objects writer).kind (objects writer).slots.length ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
        next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
        TableFamily.Model post (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) ∧
        Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) ∧
        Zone (Function.update objects writer next) base cap (cursor + NaturalLayout.stride (objects writer).kind) ∧
        next.slots.length ≤ (objects writer).slots.length ∧
        post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
        post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post ∧ ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧
        TableFamily.ValuesHave post (Function.update objects writer next) property ∧
        EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,1#64,oldValue⟩) (count+1) property ∧ TableFamily.Metadata objects (Function.update objects writer next))) := by
  have table := family.tables writer
  have capSmall : cap < 2 ^ 64 := by
    have upper := zone.valid.upper
    change base + 32 * cap ≤ 33806089496 at upper
    omega
  have countSmall : count < 2 ^ 64 := by omega
  have branches := delete_guard_normal_values source post (objects writer).kind (objects writer).plan (objects writer).slots cursor (objects writer).floor table environment
    query (BitVec.ofNat 64 count) (BitVec.ofNat 64 cap) (property writer) (values writer) queryFits queryMapped tableLocal keyLocal getCode counter capacity returned normal
  rcases branches with absent | present
  · obtain ⟨paid, positive, bounded, fits, returnedEq, frame⟩ := absent
    exact ⟨returnedEq, Or.inl ⟨paid, positive, bounded, fits, frame⟩⟩
  · obtain ⟨roomWords, getPaid, oldValue, guardedPost, getPositive, getBound, getFits, oldOwned, afterGuard, oldFrame⟩ := present
    have room : count < cap := by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, Nat.mod_eq_of_lt capSmall] at roomWords
      exact roomWords
    let ready := setVarHOLFinite (ofString "old") (Get.pair 1#64 oldValue) {source with clock := source.clock - getPaid}
    have readyFamily : TableFamily.Model ready cursor objects :=
      ⟨fun index => (family.tables index).of_fields rfl rfl rfl rfl, family.apart⟩
    have readyImage : Image ready objects base count entries :=
      image.transfer (target := ready) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
    have readyEnvironment : WarmKeys.Environment ready := environment.of_fields rfl rfl rfl
    have readyT : ready.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) := by
      simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "old" ≠ ofString "t" from by decide, tableLocal]
    have readyKey : ready.locals.lookup (ofString "key") = some (.val (.word query)) := by
      simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "old" ≠ ofString "key" from by decide, keyLocal]
    have readyOld : ready.locals.lookup (ofString "old") = some (Get.pair 1#64 oldValue) := by
      simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    obtain ⟨returnedEq, suffixPaid, next, bounded, fits, clock, kind, plan, models, nextImage, nextZone, population,
      nextCounter, codes, nextEnvironment, globals, recordFrame, finalValues, pointers⟩ :=
      delete_present_normal_values ready guardedPost cursor objects writer base cap count entries readyFamily readyImage zone room readyEnvironment
        query oldValue property values queryFits queryMapped readyT readyKey readyOld deleteCode journal counter returned afterGuard
    have finalFamily : TableFamily.Model post (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) := by
      rw [oldFrame]
      exact ⟨fun index => (models.tables index).of_fields rfl rfl rfl rfl, models.apart⟩
    have finalImage : Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) := by
      rw [oldFrame]
      exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
    have finalCounter : post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by rw [oldFrame]; exact nextCounter
    have finalCodes : post.code = source.code := by rw [oldFrame]; exact codes
    have finalEnvironment : WarmKeys.Environment post := by rw [oldFrame]; exact nextEnvironment.of_fields rfl rfl rfl
    have postClock : post.clock = guardedPost.clock := by rw [oldFrame]; rfl
    change suffixPaid ≤ source.clock - getPaid at fits
    change guardedPost.clock = source.clock - getPaid - suffixPaid at clock
    refine ⟨returnedEq, Or.inr ⟨room, getPaid + suffixPaid, next, oldValue, by omega, ?_, by omega, ?_, kind, plan, finalFamily, finalImage,
      nextZone, population, finalCounter, finalCodes, finalEnvironment, ?_,?_,?_,savedValues.append entries count property ⟨writer,BitVec.ofNat 64 cursor,1#64,oldValue⟩ (Or.inr oldOwned),pointers⟩⟩
    · dsimp only [deletePrice]
      omega
    · rw [postClock, clock]
      omega
    · intro key heap different
      change post.globals.lookup key = source.globals.lookup key
      rw [oldFrame]
      exact globals key heap different

    · constructor
      intro address earlier outside away
      rw [oldFrame]
      exact recordFrame.words address earlier outside away
    · rw [oldFrame]
      exact finalValues

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_body_normal_values
