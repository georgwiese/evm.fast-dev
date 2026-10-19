import InitECandidate.Solver.Mpt.AccountCommitEmptyPrefix
import InitECandidate.Solver.Mpt.AccountCommitPrice

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem whole_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (accountOwned : property accountWriter 1#64) (publishOwned : property accountWriter account) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account) (accountKind : (objects accountWriter).kind = .account) (differentOuter : accountWriter ≠ outer)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (accountMember : account ∈ accounts)
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32)
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableAway : Journal.Away base cap (transaction + 24#64))
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerBefore : (transaction + 32#64).toNat < cursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < cursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (empty : BitVec 64) (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 3 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (objects accountWriter).plan.capacity ≤
        Journal.Append.setPrice (objects accountWriter).kind (objects accountWriter).slots.length + 9 + (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
          (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
          Journal.Append.setPrice (objects accountWriter).kind ((objects accountWriter).slots.length + 1) + 2 else 0) +
          GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity + GrowRuntime.growthPotential (objects accountWriter).kind (next accountWriter).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) := by
  have safe : Input.LocalPrefix (ofString "a") publishCall := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape] at normal
  obtain ⟨middle,publishRun,tailRun,keepAccount⟩ := safe.normal_continue source post
    (.decCall (ofString "e") .one (ofString "acct_is_empty") [localVar "a"] afterEmpty) returned normal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr",localVar "a"] =
      some (AccountSet.values address account) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal,accountLocal,AccountSet.values]
  obtain ⟨room,publishPaid,middleCursor,published,oldFlag,oldValue,publishPositive,publishFunded,publishClock,publishForward,publishedKind,binaryFlag,
    middleFamily,middleImage,middleZone,publishPrice,population,middleCounter,middleLocals,middleCodes,middleEnvironment,middleGlobals,publishFrame,middleValues,middleSaved,middleRegistry,
    publishMetadata,publishEffect⟩ := AccountSet.call_registered source middle transaction address account cursor objects accountWriter base cap count entries family image zone countBound
      environment installed cutoff accounts registry accountApart property values publishOwned savedValues accountKind addressArena transactionGlobal accountMapped accountStored
      journal capacity counter _ args publishRun
  let middleObjects := Function.update objects accountWriter published
  let middleEntries := Function.update entries count ⟨accountWriter,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩
  have differentMarker : accountWriter ≠ writer := by
    intro same
    rw [same,writerKind] at accountKind
    cases accountKind
  have markerSame : middleObjects writer = objects writer := Function.update_of_ne (Ne.symm differentMarker) published objects
  have outerSame : middleObjects outer = objects outer := Function.update_of_ne (Ne.symm differentOuter) published objects
  have accountSelf : middleObjects accountWriter = published := by simp [middleObjects]
  have middleWriterKind : (middleObjects writer).kind = .storage := (publishMetadata.kinds writer).trans writerKind
  have middleOuterKind : (middleObjects outer).kind = .account := (publishMetadata.kinds outer).trans outerKind
  have middleAccountKind : (middleObjects accountWriter).kind = .account := (publishMetadata.kinds accountWriter).trans accountKind
  have middleFloors (table : ι) : cutoff ≤ (middleObjects table).floor := by rw [publishMetadata.floors table]; exact floors table
  have middleReferences : ∀ item,property outer item → ∃ reader,(middleObjects reader).pointer = item ∧ (middleObjects reader).kind = .word := by
    intro item ownedItem
    obtain ⟨reader,pointer,kind⟩ := innerReferences item ownedItem
    exact ⟨reader,(publishMetadata.pointers reader).trans pointer,(publishMetadata.kinds reader).trans kind⟩
  have mapped (query : BitVec 64) (current : source.memaddrs query) : middle.memaddrs query := by
    rw [middleEnvironment.domain,← environment.domain]
    exact current
  have accountWord := publishFrame.words (transaction + 16#64) accountBefore accountOutside accountAway
  have tableWord := publishFrame.words (transaction + 24#64) tableBefore tableOutside tableAway
  have outerWord := publishFrame.words (transaction + 32#64) outerBefore outerOutside outerAway
  have accountStoredNow : middle.memory (transaction + 16#64) = .word (middleObjects accountWriter).pointer := by
    rw [publishMetadata.pointers accountWriter]
    exact accountWord.2.trans accountStored
  have tableStoredNow : middle.memory (transaction + 24#64) = .word (middleObjects writer).pointer := by
    rw [publishMetadata.pointers writer]
    exact tableWord.2.trans tableStored
  have outerStoredNow : middle.memory (transaction + 32#64) = .word (middleObjects outer).pointer := by
    rw [publishMetadata.pointers outer]
    exact outerWord.2.trans outerStored
  have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [middleCodes]; exact installed
  have middleAddress : middle.locals.lookup (ofString "addr") = some (.val (.word address)) := by rw [middleLocals]; exact addressLocal
  have middleAccount : middle.locals.lookup (ofString "a") = some (.val (.word account)) := keepAccount.trans accountLocal
  obtain ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,
    nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends⟩ := empty_prefix_normal middle post address account emptyHash scratch transaction
      middleCursor cutoff middleObjects writer outer accountWriter base cap (count + 1) middleEntries middleFamily middleImage middleZone (by omega) middleEnvironment middleInstalled
      accounts middleRegistry property middleValues owned accountOwned middleSaved middleWriterKind middleOuterKind middleAccountKind differentOuter addressArena scratchArena
      middleFloors scratchBelow small journalAbove middleAddress middleAccount accountMember
      ((middleGlobals (ofString "empty_code_hash") (by decide) (by decide)).trans emptyGlobal) emptyArena middleReferences
      ((middleGlobals (ofString "sk_buf") (by decide) (by decide)).trans scratchGlobal) ((middleGlobals (ofString "ts") (by decide) (by decide)).trans transactionGlobal)
      (mapped _ tableMapped) tableStoredNow tableAbove (by omega) tableWord.1 (mapped _ outerMapped) outerStoredNow (mapped _ accountMapped) accountStoredNow
      accountAbove (by omega) accountWord.1 accountAway accountApart ((middleGlobals (ofString "journal") (by decide) (by decide)).trans journal)
      ((middleGlobals (ofString "journal_cap") (by decide) (by decide)).trans capacity) middleCounter returned tailRun
  have finalImage : Journal.Image post next base (count + (1 + added)) nextEntries := by simpa only [Nat.add_assoc] using nextImage
  have finalSaved : Journal.EntryValues nextEntries (count + (1 + added)) property := by simpa only [Nat.add_assoc] using nextSaved
  have finalCounter : post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + (1 + added))))) := by
    simpa only [Nat.add_assoc] using nextCounter
  have finalEffect : Journal.CounterEffect source post (1 + added) 0 0 := by simpa only [Nat.add_zero] using publishEffect.trans effect
  rw [markerSame,outerSame] at price
  rw [publishMetadata.kinds accountWriter,accountSelf] at price
  have mono : Journal.Append.setPrice (objects accountWriter).kind published.slots.length ≤
      Journal.Append.setPrice (objects accountWriter).kind ((objects accountWriter).slots.length + 1) := by
    rw [accountKind]
    exact account_set_price_mono _ _ population
  have extra : (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
      (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
      Journal.Append.setPrice (objects accountWriter).kind published.slots.length + 2 else 0) ≤
      (if destroyed then Get.bodyPrice (objects outer).kind (objects outer).slots.length + 3 +
      (if found then DestroyStorage.loopPrice (objects writer).slots.length iterations + Journal.Append.deletePrice (objects outer).kind (objects outer).slots.length + 1 else 0) +
      Journal.Append.setPrice (objects accountWriter).kind ((objects accountWriter).slots.length + 1) + 2 else 0) := by
    cases destroyed <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
  have totalClock : post.clock = source.clock - (publishPaid + paid) := by rw [clock,publishClock,Nat.sub_sub]
  have totalFunded : publishPaid + paid ≤ source.clock := by
    calc
      publishPaid + paid ≤ publishPaid + middle.clock := Nat.add_le_add_left funded publishPaid
      _ = source.clock := by rw [publishClock,Nat.add_sub_of_le publishFunded]
  have status : (found = false ∧ iterations = 0) ∨ (found = true ∧ ∃ reader,(objects reader).kind = .word ∧ iterations = (objects reader).slots.length) := by
    rcases branch with absent | ⟨present,reader,readerKind,visited⟩
    · exact Or.inl absent
    · have other : reader ≠ accountWriter := by
        intro same
        rw [same,publishMetadata.kinds accountWriter,accountKind] at readerKind
        cases readerKind
      have unchanged : middleObjects reader = objects reader := Function.update_of_ne other published objects
      exact Or.inr ⟨present,reader,by simpa only [unchanged] using readerKind,by simpa only [unchanged] using visited⟩
  have finalAppends : (if destroyed then 2 ≤ 1 + added else 1 + added = 1 ∧ found = false ∧ iterations = 0) := by
    cases destroyed with
    | false =>
      change added = 0 ∧ found = false ∧ iterations = 0 at appends
      exact ⟨by omega,appends.2.1,appends.2.2⟩
    | true =>
      change 1 ≤ added at appends
      change 2 ≤ 1 + added
      omega
  refine ⟨answerEq,empty,destroyed,found,iterations,publishPaid + paid,nextCursor,next,nextEntries,1 + added,by omega,totalFunded,totalClock,by omega,by omega,by omega,by omega,
    models,finalImage,nextZone,by omega,codes.trans middleCodes,nextEnvironment,middleGlobals.trans globals,nextValues,finalSaved,nextRegistry,finalEffect,publishMetadata.trans metadata,?_,?_,
    status,finalCounter,decision,binary,finalAppends⟩
  · intro query above earlier outside away
    have first := publishFrame.words query earlier outside away
    have second := frame query above (by omega) first.1 away
    exact ⟨second.1,second.2.trans first.2⟩
  · intro table notWriter notOuter notAccount
    exact (others table notWriter notOuter notAccount).trans (Function.update_of_ne notAccount published objects)

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.whole_normal
