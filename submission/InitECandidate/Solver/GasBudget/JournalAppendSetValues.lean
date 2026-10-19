import InitECandidate.Solver.GasBudget.JournalAppendSetPrice
import InitECandidate.Solver.GasBudget.JournalAppendSetRecordValues
import InitECandidate.Solver.GasBudget.JournalAppendEntryValues
import InitECandidate.Solver.GasBudget.JournalEntryValues
import InitECandidate.Solver.GasBudget.JournalAppendKeyFields

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete original jset body on actual normal execution. The getter,
guard, key allocation/copy, real record stores, increment and final setter
derive the next journal image and whole table family. No helper execution,
intermediate model, future allocation room or source-clock budget is given. -/
theorem set_body_normal_values {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (query value : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer value)
    (savedValues : EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source setBody = (some (.returned returned), post)) :
    count < cap ∧ returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      (oldFlag = 0#64 ∨ oldFlag = 1#64) ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, oldFlag, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        setPrice (objects writer).kind (objects writer).slots.length + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post ∧ ProtectedFrame base cap cursor objects (Function.update objects writer next) source post ∧
      TableFamily.ValuesHave post (Function.update objects writer next) property ∧
      EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) (count+1) property ∧ TableFamily.Metadata objects (Function.update objects writer next) := by
  have table := family.tables writer
  have capSmall : cap < 2 ^ 64 := by
    have upper := zone.valid.upper
    change base + 32 * cap ≤ 33806089496 at upper
    omega
  have countSmall : count < 2 ^ 64 := by omega
  obtain ⟨roomWords, getPaid, flag, oldValue, guardedPost, getPositive, getBound, getFits, binary, oldOwned, afterGuard, oldFrame⟩ :=
    set_guard_normal_values source post (objects writer).kind (objects writer).plan (objects writer).slots cursor (objects writer).floor table environment
      query (BitVec.ofNat 64 count) (BitVec.ofNat 64 cap) (property writer) (values writer) queryFits queryMapped tableLocal keyLocal getCode counter capacity returned normal
  have room : count < cap := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, Nat.mod_eq_of_lt capSmall] at roomWords
    exact roomWords
  let ready := setVarHOLFinite (ofString "old") (Get.pair flag oldValue) {source with clock := source.clock - getPaid}
  have readyFamily : TableFamily.Model ready cursor objects :=
    ⟨fun index => (family.tables index).of_fields rfl rfl rfl rfl, family.apart⟩
  have readyImage : Image ready objects base count entries :=
    image.transfer (target := ready) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyEnvironment : WarmKeys.Environment ready := environment.of_fields rfl rfl rfl
  have readyT : ready.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) := by
    simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "old" ≠ ofString "t" from by decide, tableLocal]
  have readyKey : ready.locals.lookup (ofString "key") = some (.val (.word query)) := by
    simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "old" ≠ ofString "key" from by decide, keyLocal]
  have readyValue : ready.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "old" ≠ ofString "value" from by decide, valueLocal]
  have readyOld : ready.locals.lookup (ofString "old") = some (Get.pair flag oldValue) := by
    simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  rw [set_key_shape] at afterGuard
  obtain ⟨nextBound, keyFits, keyBound, region, keyPost, keyRun, keyFrame⟩ :=
    key_normal ready guardedPost (objects writer).kind (objects writer).plan (objects writer).slots cursor (objects writer).floor (readyFamily.tables writer)
      readyEnvironment query queryFits queryMapped readyT readyKey setAfterCopy returned afterGuard
  let copied := keyState ready (objects writer).kind cursor query
  have copiedFamily : TableFamily.Model copied (cursor + NaturalLayout.stride (objects writer).kind) objects :=
    key_models ready (objects writer).kind cursor query objects readyFamily region
  have copiedPools : ∀ index,MemoryModel.PoolFrame ready.memory copied.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply key_earlier ready (objects writer).kind cursor query _ region
    rw [NaturalLayout.number (objects index).kind _ (readyFamily.tables index).valid pool offset inside]
    have := (readyFamily.tables index).earlier pool
    omega
  have copiedValues := values.of_pools ready copied objects cursor readyFamily property copiedPools
  have copiedFrame : ProtectedFrame base cap cursor objects objects source copied := by
    constructor
    intro address before outside away
    exact ⟨outside,key_earlier ready (objects writer).kind cursor query address region before⟩
  have copiedImage : Image copied objects base count entries :=
    key_image ready (objects writer).kind cursor query objects base count entries readyImage region (by have before := zone.earlier; omega)
  have copiedZone : Zone objects base cap (cursor + NaturalLayout.stride (objects writer).kind) := zone.advance (by omega)
  have copiedEnvironment : WarmKeys.Environment copied := environment.of_fields rfl rfl rfl
  have copiedT : copied.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)) :=
    (key_local ready (objects writer).kind cursor query "t" (by decide) (by decide)).trans readyT
  have copiedKey : copied.locals.lookup (ofString "key") = some (.val (.word query)) :=
    (key_local ready (objects writer).kind cursor query "key" (by decide) (by decide)).trans readyKey
  have copiedValue : copied.locals.lookup (ofString "value") = some (.val (.word value)) :=
    (key_local ready (objects writer).kind cursor query "value" (by decide) (by decide)).trans readyValue
  have copiedOld : copied.locals.lookup (ofString "old") = some (Get.pair flag oldValue) :=
    (key_local ready (objects writer).kind cursor query "old" (by decide) (by decide)).trans readyOld
  have copiedPointer : copied.locals.lookup (ofString "kc") = some (.val (.word (BitVec.ofNat 64 cursor))) := bind_lookup_same _ _ _
  have copiedJournal : copied.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))) :=
    (key_globals ready (objects writer).kind cursor query (ofString "journal") (by decide)).trans journal
  have copiedCounter : copied.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))) :=
    (key_globals ready (objects writer).kind cursor query (ofString "journal_n") (by decide)).trans counter
  obtain ⟨copiedFits, copiedMapped⟩ := copied_key_geometry ready (objects writer).kind cursor query region environment.domain
  obtain ⟨returnedEq, setPaid, nextCursor, next, setFits, finalClock, forward, kind, nextFamily, nextImage, nextZone, bounded, population,
    nextCounter, codes, nextEnvironment, globals, recordFrame, finalValues, pointers⟩ :=
    set_record_normal_values copied keyPost (cursor + NaturalLayout.stride (objects writer).kind) objects writer base cap count entries copiedFamily copiedImage copiedZone room copiedEnvironment
      query value (BitVec.ofNat 64 cursor) flag oldValue property copiedValues owned queryFits queryMapped copiedFits copiedMapped copiedT copiedKey copiedValue copiedPointer copiedOld copiedJournal copiedCounter returned keyRun
  have protectedFrame := copiedFrame.trans recordFrame (by have := key_rounding (objects writer).kind; omega)
  have finalFamily : TableFamily.Model post nextCursor (Function.update objects writer next) := by
    rw [oldFrame, keyFrame]
    exact ⟨fun index => (nextFamily.tables index).of_fields rfl rfl rfl rfl, nextFamily.apart⟩
  have finalImage : Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, flag, oldValue⟩) := by
    rw [oldFrame, keyFrame]
    exact nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalCounter : post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) := by
    rw [oldFrame, keyFrame]
    exact nextCounter
  have finalCodes : post.code = source.code := by rw [oldFrame, keyFrame]; exact codes
  have finalEnvironment : WarmKeys.Environment post := by
    rw [oldFrame, keyFrame]
    exact nextEnvironment.of_fields rfl rfl rfl
  have postClock : post.clock = keyPost.clock := by rw [oldFrame, keyFrame]; rfl
  have copiedClock : copied.clock = source.clock - getPaid - keyPrice (objects writer).kind cursor query := key_clock ready _ cursor query
  change keyPrice (objects writer).kind cursor query ≤ source.clock - getPaid at keyFits
  rw [copiedClock] at setFits finalClock
  refine ⟨room, returnedEq, getPaid + keyPrice (objects writer).kind cursor query + setPaid, nextCursor, next, flag, oldValue,
    by omega, ?_, by omega, kind, binary, finalFamily, finalImage, nextZone, ?_, population, finalCounter, finalCodes, finalEnvironment, ?_,?_,?_,savedValues.append entries count property ⟨writer,BitVec.ofNat 64 cursor,flag,oldValue⟩ oldOwned,pointers⟩
  · rw [postClock, finalClock]
    omega
  · dsimp only [setPrice]
    omega
  · intro key heap different
    have finalGlobal : post.globals.lookup key = keyPost.globals.lookup key := by rw [oldFrame, keyFrame]; rfl
    exact finalGlobal.trans ((globals key heap different).trans (key_globals ready (objects writer).kind cursor query key heap))

  · constructor
    intro address earlier outside away
    rw [oldFrame,keyFrame]
    exact protectedFrame.words address earlier outside away
  · rw [oldFrame,keyFrame]
    exact finalValues

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_body_normal_values
