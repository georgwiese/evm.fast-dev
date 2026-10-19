import InitECandidate.Solver.Mpt.StorageSetAfterAccount
import InitECandidate.Solver.Mpt.StorageSetResultMutation
import InitECandidate.Solver.GasBudget.AccountOptionalCallNormalValues
import InitECandidate.Solver.GasBudget.JournalPersistentFrame

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

def wholePrice (population : Nat) (created : Bool) : Nat :=
  43 * population + 31148 + (Get.bodyPrice .account (population + 3) + 1 + tailPrice (population + 3) created)

theorem whole_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit populationBound : Nat) (objects : ι → TableFamily.Object) (writer reader blockReader recorder : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤populationBound)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account) (blockReaderKind : (objects blockReader).kind=.account) (recorderKind : (objects recorder).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
    (writerOwned : property writer 1#64) (recorderOwned : property recorder 1#64)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit) (afterWorld : frozenEnd≤cursor) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (hashEnvironment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0) (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0)
    (addressArena : AllocatedBytes.Arena address 20) (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
    (arena : Rlp.Validation.Arena source scratchPtr limit) (scratchBelow : scratchPtr.toNat≤cutoff) (aligned : cutoff%8=0) (sizeBound : 16*valueLimit<2^64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (transactionGlobal : source.globals.lookup (ofString "ts")=some (.val (.word transaction)))
    (blockGlobal : source.globals.lookup (ofString "bs")=some (.val (.word block))) (blockArena : AllocatedBytes.Arena block 80) (blockBefore : block.toNat+80≤(objects writer).floor)
    (transactionArena : AllocatedBytes.Arena transaction 72) (transactionBefore : transaction.toNat+72≤(objects writer).floor)
    (setMapped : source.memaddrs (transaction+8#64)) (setCell : source.memory (transaction+8#64)=.word (objects writer).pointer)
    (getMapped : source.memaddrs (transaction+16#64)) (getCell : source.memory (transaction+16#64)=.word (objects reader).pointer)
    (blockGetMapped : source.memaddrs (block+16#64)) (blockGetCell : source.memory (block+16#64)=.word (objects blockReader).pointer)
    (recordMapped : source.memaddrs (block+72#64)) (recordCell : source.memory (block+72#64)=.word (objects recorder).pointer)
    (key : BitVec 64) (words : Input.RlpWrite.U256Value.Words) (keyArena : AllocatedBytes.Arena key 32)
    (outer : ι) (outerKind : (objects outer).kind = .account)
    (references : ∀ value,property outer value → ∃ index,(objects index).pointer = value ∧ (objects index).kind = .word)
    (freshOwned : ∀ index,(objects index).kind = .word → ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property index pointer)
    (base cap journalCount : Nat) (entries : Nat → Journal.Entry ι)
    (image : Journal.Image source objects base journalCount entries) (zone : Journal.Zone objects base cap cursor) (countBound : journalCount ≤ cap) (journalAbove : cutoff ≤ base)
    (savedValues : Journal.EntryValues entries journalCount property)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (storageMapped : source.memaddrs (transaction + 32#64)) (storageStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (storageAbove : cutoff ≤ (transaction + 32#64).toNat) (storageBefore : (transaction + 32#64).toNat < cursor) (storageOutside : TableFamily.Outside objects (transaction + 32#64))
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 journalCount))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ nextAccounts,AccountDecode.Registry.Extension accounts nextAccounts cursor ∧
      Result source post cursor cutoff (populationBound + 3) objects outer base cap journalCount nextAccounts property (wholePrice populationBound) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr"] = some [.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal]
  rw [body_shape] at normal
  obtain ⟨prefixPaid,middleCursor,middleObjects,nextAccounts,ready,word,finish,prefixFunded,prefixClock,prefixForward,middleFamily,middlePopulation,middleFloors,pointers,⟨middleWorld⟩,middleHash,middleArena,
    prefixGlobals,prefixCode,prefixPrice,middleRegistry,middleValues,extension,prefixFrame,prefixMetadata,ownership,accountCell,readyLocals,tailRun,scope⟩ :=
    AccountCache.scoped_transaction_normal_values_framed source post transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit populationBound objects writer reader blockReader recorder
      family population writerKind readerKind blockReaderKind recorderKind environment installed accounts registry property tableValues writerOwned recorderOwned world afterWorld floors hashEnvironment
      stateArena stateAligned padArena padAligned addressArena stateBelow padBelow arena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore
      setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell "a" [localVar "addr"] afterAccount args returned normal
  have domain : ready.memaddrs = source.memaddrs := middleWorld.domain.trans environment.domain.symm
  have endian : ready.be = source.be := middleWorld.little.trans environment.little.symm
  have middleEnvironment := environment.of_fields prefixCode domain endian
  have middleInstalled : Input.OriginalCode.Installed ready.code := by rw [prefixCode]; exact installed
  obtain ⟨middleImage,middleZone⟩ := Journal.image_zone_framed source ready cursor middleCursor cutoff base cap journalCount objects middleObjects entries image zone countBound prefixForward journalAbove prefixFrame prefixMetadata domain
  have middleOuterKind : (middleObjects outer).kind = .account := (prefixMetadata.kinds outer).trans outerKind
  have middleReferences : ∀ value,property outer value → ∃ index,(middleObjects index).pointer = value ∧ (middleObjects index).kind = .word := by
    intro value prior
    obtain ⟨index,pointer,kind⟩ := references value prior
    exact ⟨index,(prefixMetadata.pointers index).trans pointer,(prefixMetadata.kinds index).trans kind⟩
  have middleFreshOwned : ∀ index,(middleObjects index).kind = .word → ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property index pointer := by
    intro index kind pointer arena aligned
    exact freshOwned index ((prefixMetadata.kinds index).symm.trans kind) pointer arena aligned
  have middleApart := extension.journal_apart accountApart zone.earlier
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "addr" by decide] using addressLocal
  have readyKey : ready.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "key" by decide] using keyLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "value" by decide] using valueLocal
  have readyMapped : ready.memaddrs (transaction + 32#64) := by rw [domain]; exact storageMapped
  have readyStored : ready.memory (transaction + 32#64) = .word (middleObjects outer).pointer := by
    rw [prefixMetadata.pointers outer]
    exact (prefixFrame.words _ storageAbove storageBefore storageOutside).2.trans storageStored
  obtain ⟨answerEq,result⟩ := after_account_normal ready finish address key words middleCursor cutoff (populationBound + 3) middleObjects outer base cap journalCount entries middleFamily middleImage middleZone countBound middlePopulation
    middleEnvironment middleInstalled nextAccounts middleRegistry middleApart property middleValues savedValues middleReferences middleFreshOwned middleOuterKind addressArena keyArena readyAddress readyKey readyValue transaction
    ((prefixGlobals (ofString "ts") (by decide)).trans transactionGlobal) readyMapped readyStored
    ((prefixGlobals (ofString "journal") (by decide)).trans journal) ((prefixGlobals (ofString "journal_cap") (by decide)).trans capacity) ((prefixGlobals (ofString "journal_n") (by decide)).trans counter) returned tailRun
  have wholeResult := result.prepend_mutation (source := source) prefixPaid (43 * populationBound + 31148) prefixFunded prefixPrice prefixClock prefixForward prefixFrame prefixMetadata prefixGlobals prefixCode
  rw [scope]
  refine ⟨answerEq,nextAccounts,extension,?_⟩
  change Result source {finish with locals := HolFiniteMapExact.resVarEq finish.locals (ofString "a",source.locals.lookup (ofString "a"))} cursor cutoff (populationBound + 3) objects outer base cap journalCount nextAccounts property
    (fun created => 43 * populationBound + 31148 + (Get.bodyPrice .account (populationBound + 3) + 1 + tailPrice (populationBound + 3) created))
  exact wholeResult.locals _

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.whole_normal
