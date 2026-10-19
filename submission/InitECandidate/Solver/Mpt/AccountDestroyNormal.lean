import InitECandidate.Solver.Mpt.AccountCommitProgram
import InitECandidate.Solver.Mpt.DestroyStorageCall
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem destroy_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (accountOwned : property accountWriter 1#64) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account) (accountKind : (objects accountWriter).kind = .account) (differentOuter : accountWriter ≠ outer)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < cursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source destroyBody = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 2 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
        Get.bodyPrice (objects outer).kind (objects outer).slots.length + 2 + (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity +
          Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 2 + GrowRuntime.growthPotential (objects accountWriter).kind (next accountWriter).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) := by
  have firstSafe : Input.LocalPrefix (ofString "addr") destroyStorageCall := .call none _ _ (by intro name impossible; cases impossible)
  rw [destroy_shape] at normal
  obtain ⟨middle,storageRun,tailRun,keepAddress⟩ := firstSafe.normal_continue source post (.seq eraseAccountCall (.return (.const 0#64))) returned normal
  have storageArgs : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr"] = some [.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal]
  obtain ⟨found,iterations,storagePaid,middleCursor,middleObjects,middleEntries,storageAdded,storagePositive,storageFunded,storageClock,storageForward,storageAddedBound,storageCapacity,
    middleFamily,middleImage,middleZone,storagePrice,middleLocals,middleCodes,middleEnvironment,middleGlobals,middleValues,middleSaved,middleRegistry,storageEffect,middleMetadata,
    storageFrame,storageOthers,branch,middleCounter⟩ := DestroyStorage.call_normal source middle address scratch transaction cursor cutoff objects writer outer base cap count entries
      family image zone countBound environment installed accounts registry property values owned savedValues writerKind outerKind addressArena scratchArena floors scratchBelow small journalAbove
      innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableBefore tableOutside outerMapped outerStored accountApart journal capacity counter _ storageArgs storageRun
  have secondSafe : Input.LocalPrefix (ofString "addr") eraseAccountCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,setRun,returnRun,lastAddress⟩ := secondSafe.normal_continue middle post (.return (.const 0#64)) returned tailRun
  have middleAddress := keepAddress.trans addressLocal
  have args : evalListHOLFinite middle (h := fun query => Classical.propDecidable (middle.memaddrs query)) [localVar "addr",.const 1#64] = some (AccountSet.values address 1#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,middleAddress,AccountSet.values]
  have differentMarker : accountWriter ≠ writer := by
    intro same
    rw [same,writerKind] at accountKind
    cases accountKind
  have accountSame := storageOthers accountWriter differentMarker differentOuter
  have middleAccountKind : (middleObjects accountWriter).kind = .account := by rw [accountSame]; exact accountKind
  have middleTransaction := (middleGlobals (ofString "ts") (by decide) (by decide)).trans transactionGlobal
  have middleMapped : middle.memaddrs (transaction + 16#64) := by
    rw [middleEnvironment.domain,← environment.domain]
    exact accountMapped
  have accountWord := storageFrame (transaction + 16#64) accountAbove accountBefore accountOutside accountAway
  have middleStored : middle.memory (transaction + 16#64) = .word (middleObjects accountWriter).pointer := by
    rw [middleMetadata.pointers accountWriter]
    exact accountWord.2.trans accountStored
  have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [middleCodes]; exact installed
  obtain ⟨room,setPaid,nextCursor,nextAccount,oldFlag,oldValue,setPositive,setFunded,setClock,setForward,nextKind,binary,models,nextImage,nextZone,setPrice,population,
    nextCounter,setLocals,setCodes,nextEnvironment,setGlobals,setFrame,nextValues,nextSaved,nextRegistry,setMetadata,setEffect⟩ := AccountSet.call_registered middle mutated transaction address 1#64
      middleCursor middleObjects accountWriter base cap (count + storageAdded) middleEntries middleFamily middleImage middleZone storageCapacity middleEnvironment middleInstalled
      cutoff accounts middleRegistry accountApart property middleValues accountOwned middleSaved middleAccountKind addressArena middleTransaction middleMapped middleStored
      ((middleGlobals (ofString "journal") (by decide) (by decide)).trans journal) ((middleGlobals (ofString "journal_cap") (by decide) (by decide)).trans capacity)
      middleCounter _ args setRun
  have returnInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnInfo.1.symm.trans rfl)
  rw [returnInfo.2]
  let finish := emptyLocalsHOLFinite mutated
  let next := Function.update middleObjects accountWriter nextAccount
  let nextEntries := Function.update middleEntries (count + storageAdded) ⟨accountWriter,BitVec.ofNat 64 middleCursor,oldFlag,oldValue⟩
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + (storageAdded + 1)) nextEntries := by
    have current := nextImage.transfer (target := finish) rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
    simpa only [Nat.add_assoc] using current
  have finalRegistry := nextRegistry.framed mutated finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next mutated finish rfl) (Nat.le_refl _) rfl
  have finalSaved : Journal.EntryValues nextEntries (count + (storageAdded + 1)) property := by simpa only [Nat.add_assoc] using nextSaved
  have finalCounter : finish.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + (storageAdded + 1))))) := by
    simpa only [finish,emptyLocalsHOLFinite,Nat.add_assoc] using nextCounter
  have finalEffect : Journal.CounterEffect source finish (storageAdded + 1) 0 0 := by
    change Journal.CounterEffect source mutated (storageAdded + 1) 0 0
    simpa only [Nat.add_zero] using storageEffect.trans setEffect
  have finalMarker : next writer = middleObjects writer := Function.update_of_ne (Ne.symm differentMarker) nextAccount middleObjects
  have finalAccount : next accountWriter = nextAccount := by simp [next]
  rw [accountSame] at setPrice
  have price : storagePaid + setPaid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
      Get.bodyPrice (objects outer).kind (objects outer).slots.length + 2 +
        (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
        GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity + Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 2 +
        GrowRuntime.growthPotential (objects accountWriter).kind (next accountWriter).plan.capacity := by
    rw [finalMarker,finalAccount]
    omega
  have status : (found = false ∧ iterations = 0) ∨ (found = true ∧ ∃ reader,(objects reader).kind = .word ∧ iterations = (objects reader).slots.length) := by
    rcases branch with absent | present
    · exact Or.inl ⟨absent.1,absent.2.1⟩
    · exact Or.inr present
  have totalClock : mutated.clock = source.clock - (storagePaid + setPaid) := by
    rw [setClock,storageClock,Nat.sub_sub]
  have totalFunded : storagePaid + setPaid ≤ source.clock := by
    calc
      storagePaid + setPaid ≤ storagePaid + middle.clock := Nat.add_le_add_left setFunded storagePaid
      _ = source.clock := by rw [storageClock,Nat.add_sub_of_le storageFunded]
  have totalForward : cursor ≤ nextCursor := Nat.le_trans storageForward setForward
  have totalCapacity : count + (storageAdded + 1) ≤ cap := by omega
  refine ⟨answerEq,found,iterations,storagePaid + setPaid,nextCursor,next,nextEntries,storageAdded + 1,by omega,totalFunded,totalClock,totalForward,by omega,by omega,totalCapacity,
    finalFamily,finalImage,nextZone,price,setCodes.trans middleCodes,nextEnvironment.of_fields rfl rfl rfl,middleGlobals.trans setGlobals,nextValues,finalSaved,finalRegistry,finalEffect,
    middleMetadata.trans setMetadata,?_,?_,status,finalCounter⟩
  · intro query above earlier outside away
    have first := storageFrame query above earlier outside away
    have second := setFrame.words query (by omega) first.1 away
    exact ⟨second.1,second.2.trans first.2⟩
  · intro table notWriter notOuter notAccount
    exact (Function.update_of_ne notAccount nextAccount middleObjects).trans (storageOthers table notWriter notOuter)

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.destroy_normal
