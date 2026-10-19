import InitECandidate.Solver.Mpt.TransientSetZeroPrefix
import InitECandidate.Solver.Mpt.StorageKeyCall
import InitECandidate.Solver.GasBudget.JournalRangeImage

namespace InitECandidate.Solver.Mpt.TransientSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem whole_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch transaction : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (freshOwned : ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property writer pointer)
    (writerKind : (objects writer).kind = .storage)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 64#64)) (tableStored : source.memory (transaction + 64#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 64#64).toNat)
    (tableBefore : (transaction + 64#64).toNat < cursor)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (removed : Bool) (paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        14 + (if removed then Journal.Append.deletePrice (objects writer).kind (objects writer).slots.length + 1 else Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 2) + GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ reader,reader ≠ writer → next reader = objects reader) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧
      (next writer).slots.length ≤ (objects writer).slots.length + 1 ∧ removed = decide (U256Zero.resultWord words ≠ 0#64) ∧ (removed = false → added = 1) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr",localVar "key"] =
      some [.val (.word address),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal,keyLocal]
  rw [body_shape] at normal
  obtain ⟨keyFunded,keyBound,ready,inner,readyKey,readyLocals,readyClock,readyGlobals,readyCode,readyDomain,readyEndian,
    readyFamily,readyValues,readyRegistry,keyFrame,wordAgreement,tailRun,scope⟩ := StorageKey.scoped_registered source post address key scratch scratchGlobal
      environment.domain addressArena keyArena scratchArena installed cutoff cursor objects accounts family registry property values floors scratchBelow small
      "k" _ afterKey args (some (.returned returned)) (Or.inr ⟨returned,rfl⟩) normal
  have readyEnvironment := environment.of_fields readyCode readyDomain readyEndian
  have readyImage : Journal.Image ready objects base count entries := image.of_above
    (by have upper := zone.valid.upper; change base + 32 * cap ≤ 33806089496 at upper; omega) journalAbove readyDomain wordAgreement
  have readyTransaction : ready.globals.lookup (ofString "ts") = some (.val (.word transaction)) := by rw [readyGlobals]; exact transactionGlobal
  have readyMapped : ready.memaddrs (transaction + 64#64) := by rw [readyDomain]; exact tableMapped
  have readyStored : ready.memory (transaction + 64#64) = .word (objects writer).pointer := (wordAgreement _ tableAbove).trans tableStored
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) := by
    rw [readyLocals]
    simp only [HolFiniteMapExact.lookup_update,show ofString "value" ≠ ofString "k" by decide,↓reduceIte]
    exact valueLocal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [readyCode]; exact installed
  have readyJournal : ready.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))) := by rw [readyGlobals]; exact journal
  have readyCapacity : ready.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))) := by rw [readyGlobals]; exact capacity
  have readyCounter : ready.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))) := by rw [readyGlobals]; exact counter
  obtain ⟨answerEq,removed,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,frame,metadata,others,nextCounter,population,decision,appends⟩ := zero_prefix_normal ready inner scratch transaction words
      cursor cutoff objects writer base cap count entries readyFamily readyImage zone countBound readyEnvironment readyInstalled accounts readyRegistry accountApart property readyValues savedValues
      freshOwned writerKind scratchArena readyKey readyValue readyTransaction readyMapped readyStored tableBefore readyJournal readyCapacity readyCounter returned tailRun
  rw [scope]
  let finish := restore source "k" inner
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next inner finish rfl) (Nat.le_refl _) rfl
  rw [readyClock] at funded clock
  have totalFunded : StorageKey.price address key scratch + 1 + paid ≤ source.clock := by
    calc
      _ ≤ StorageKey.price address key scratch + 1 + (source.clock - (StorageKey.price address key scratch + 1)) := Nat.add_le_add_left funded _
      _ = source.clock := Nat.add_sub_of_le keyFunded
  have totalClock : inner.clock = source.clock - (StorageKey.price address key scratch + 1 + paid) := by rw [clock,Nat.sub_sub]
  have finalGlobals : Journal.OtherGlobals source finish := by
    intro name notHeap notCounter
    exact (globals name notHeap notCounter).trans (congrArg (fun map => map.lookup name) readyGlobals)
  have finalEffect : Journal.CounterEffect source finish added 0 0 := by
    change Journal.currentCount inner + 0 + 0 = Journal.currentCount source + added
    simpa only [Journal.CounterEffect,Journal.currentCount,readyGlobals] using effect
  refine ⟨answerEq,removed,StorageKey.price address key scratch + 1 + paid,nextCursor,next,nextEntries,added,by omega,totalFunded,totalClock,forward,addedBound,capacityBound,finalFamily,
    finalImage,nextZone,by omega,codes.trans readyCode,nextEnvironment.of_fields rfl rfl rfl,finalGlobals,nextValues,nextSaved,finalRegistry,finalEffect,metadata,?_,others,nextCounter,population,decision,appends⟩
  intro query above earlier outside away
  obtain ⟨nextOutside,equal⟩ := frame.words query earlier outside away
  exact ⟨nextOutside,equal.trans (wordAgreement query above)⟩

end InitECandidate.Solver.Mpt.TransientSet

#print axioms InitECandidate.Solver.Mpt.TransientSet.whole_normal
