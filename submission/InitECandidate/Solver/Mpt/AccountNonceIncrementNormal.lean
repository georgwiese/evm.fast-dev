import InitECandidate.Solver.Mpt.AccountNonceIncrementAfterGetFamily
import InitECandidate.Solver.Mpt.AccountBalanceSetPrice
import InitECandidate.Solver.Mpt.AccountBalanceSetResultControl
import InitECandidate.Solver.GasBudget.AccountRequiredCallRegistered

namespace InitECandidate.Solver.Mpt.AccountNonceIncrement
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget AccountBalanceSet

theorem whole_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit populationBound : Nat) (objects : ι → TableFamily.Object) (writer reader blockReader recorder : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤populationBound)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account) (blockReaderKind : (objects blockReader).kind=.account) (recorderKind : (objects recorder).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
    (writerOwned : property writer 1#64) (recorderOwned : property recorder 1#64)
    (cacheKnown : ∀ value,property reader value → AccountDecode.Registry.Known accounts value)
    (blockCacheKnown : ∀ value,property blockReader value → AccountDecode.Registry.Known accounts value)
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
    (marker outer : ι) (markerKind : (objects marker).kind = .storage) (outerKind : (objects outer).kind = .account)
    (differentOuter : reader ≠ outer) (markerOwned : property marker 1#64) (accountOwned : property reader 1#64)
    (references : ∀ value,property outer value → ∃ index,(objects index).pointer = value ∧ (objects index).kind = .word)
    (scratch : BitVec 64) (scratchArena : AllocatedBytes.Arena scratch 52) (keyScratchBelow : scratch.toNat + 52 ≤ cutoff)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (image : Journal.Image source objects base count entries) (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (journalAbove : cutoff ≤ base)
    (savedValues : Journal.EntryValues entries count property)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (markerMapped : source.memaddrs (transaction + 24#64)) (markerStored : source.memory (transaction + 24#64) = .word (objects marker).pointer)
    (markerAbove : cutoff ≤ (transaction + 24#64).toNat) (markerBefore : (transaction + 24#64).toNat < cursor)
    (markerOutside : TableFamily.Outside objects (transaction + 24#64)) (markerAway : Journal.Away base cap (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64)) (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerAbove : cutoff ≤ (transaction + 32#64).toNat) (outerBefore : (transaction + 32#64).toNat < cursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < cursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ Result source post cursor cutoff (populationBound + 3) objects reader base cap count accounts property (wholePrice populationBound) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr"] = some [.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal]
  rw [body_shape] at normal
  obtain ⟨prefixPaid,middleCursor,middleObjects,middleAccounts,ready,account,finish,prefixFunded,prefixClock,prefixForward,middleFamily,middlePopulation,middleFloors,pointers,⟨middleWorld⟩,middleHash,middleArena,
    prefixGlobals,prefixCode,prefixPrice,middleRegistry,middleValues,extension,prefixFrame,prefixMetadata,member,accountImage,accountCell,readyLocals,tailRun,scope⟩ :=
    AccountRequired.scoped_transaction_registered_framed source post transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit populationBound objects writer reader blockReader recorder
      family population writerKind readerKind blockReaderKind recorderKind environment installed accounts registry property tableValues writerOwned recorderOwned cacheKnown blockCacheKnown world afterWorld floors hashEnvironment
      stateArena stateAligned padArena padAligned addressArena stateBelow padBelow arena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore
      setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell "a" [localVar "addr"] afterGet args returned normal
  have domain : ready.memaddrs = source.memaddrs := middleWorld.domain.trans environment.domain.symm
  have endian : ready.be = source.be := middleWorld.little.trans environment.little.symm
  have middleEnvironment := environment.of_fields prefixCode domain endian
  have middleInstalled : Input.OriginalCode.Installed ready.code := by rw [prefixCode]; exact installed
  obtain ⟨middleImage,middleZone⟩ := Journal.image_zone_framed source ready cursor middleCursor cutoff base cap count objects middleObjects entries image zone countBound prefixForward journalAbove prefixFrame prefixMetadata domain
  have middleReferences : ∀ value,property outer value → ∃ index,(middleObjects index).pointer = value ∧ (middleObjects index).kind = .word := by
    intro value owned
    obtain ⟨index,pointer,kind⟩ := references value owned
    exact ⟨index,(prefixMetadata.pointers index).trans pointer,(prefixMetadata.kinds index).trans kind⟩
  have middleApart := extension.journal_apart accountApart zone.earlier
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "addr" by decide] using addressLocal
  have markerWord := prefixFrame.words (transaction + 24#64) markerAbove markerBefore markerOutside
  have outerWord := prefixFrame.words (transaction + 32#64) outerAbove outerBefore outerOutside
  have accountWord := prefixFrame.words (transaction + 16#64) accountAbove accountBefore accountOutside
  have mapped (query : BitVec 64) (mapping : source.memaddrs query) : ready.memaddrs query := by rw [domain]; exact mapping
  have middleMarkerStored : ready.memory (transaction + 24#64) = .word (middleObjects marker).pointer := by
    rw [prefixMetadata.pointers marker]
    exact markerWord.2.trans markerStored
  have middleOuterStored : ready.memory (transaction + 32#64) = .word (middleObjects outer).pointer := by
    rw [prefixMetadata.pointers outer]
    exact outerWord.2.trans outerStored
  have middleAccountStored : ready.memory (transaction + 16#64) = .word (middleObjects reader).pointer := by
    rw [prefixMetadata.pointers reader]
    exact accountWord.2.trans getCell
  obtain ⟨answerEq,result⟩ := after_get_family ready finish address account emptyHash scratch transaction middleCursor cutoff (populationBound + 3) middleObjects marker outer reader
    base cap count entries middlePopulation middleFamily middleImage middleZone countBound middleEnvironment middleInstalled middleAccounts middleRegistry property middleValues markerOwned accountOwned savedValues
    ((prefixMetadata.kinds marker).trans markerKind) ((prefixMetadata.kinds outer).trans outerKind) ((prefixMetadata.kinds reader).trans readerKind) differentOuter addressArena scratchArena
    (fun index => Nat.le_trans world.ordered (middleFloors index)) keyScratchBelow (by have := world.ordered; have := world.bounded; omega) journalAbove member readyAddress accountCell
    ((prefixGlobals (ofString "empty_code_hash") (by decide)).trans hashGlobal) hashArena middleReferences ((prefixGlobals (ofString "sk_buf") (by decide)).trans scratchGlobal)
    ((prefixGlobals (ofString "ts") (by decide)).trans transactionGlobal)
    (mapped _ markerMapped) middleMarkerStored markerAbove markerAway (by omega) markerWord.1
    (mapped _ outerMapped) middleOuterStored (by omega) outerWord.1 outerAway
    (mapped _ getMapped) middleAccountStored accountAbove (by omega) accountWord.1 accountAway middleApart
    ((prefixGlobals (ofString "journal") (by decide)).trans journal) ((prefixGlobals (ofString "journal_cap") (by decide)).trans capacity) ((prefixGlobals (ofString "journal_n") (by decide)).trans counter) returned tailRun
  have bounded := result.mono (suffixPrice (populationBound + 3) (populationBound + 3) (populationBound + 3))
    (suffix_price_mono _ _ _ _ (middlePopulation marker) (middlePopulation outer) (middlePopulation reader))
  have wholeResult := bounded.prepend_mutation (source := source) prefixPaid (43 * populationBound + 31152) prefixFunded prefixPrice prefixClock prefixForward extension prefixFrame prefixMetadata prefixGlobals prefixCode
  rw [scope]
  refine ⟨answerEq,?_⟩
  change Result source {finish with locals := HolFiniteMapExact.resVarEq finish.locals (ofString "a",source.locals.lookup (ofString "a"))} cursor cutoff (populationBound + 3) objects reader base cap count accounts property
    (fun destroyed found iterations => 43 * populationBound + 31152 + suffixPrice (populationBound + 3) (populationBound + 3) (populationBound + 3) destroyed found iterations)
  exact wholeResult.locals _

end InitECandidate.Solver.Mpt.AccountNonceIncrement

#print axioms InitECandidate.Solver.Mpt.AccountNonceIncrement.whole_normal
