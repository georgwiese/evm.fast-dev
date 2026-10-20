import InitECandidate.Solver.Mpt.AccountCodeAfterGet
import InitECandidate.Solver.Mpt.AccountCodePrice
import InitECandidate.Solver.Mpt.AccountMutationHeapPrefix
import InitECandidate.Solver.Mpt.AccountMutationMonotone
import InitECandidate.Solver.GasBudget.AccountRequiredCallRegistered

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_branch_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash hashValue : BitVec 64)
    (cursor cutoff protectedCursor frozenEnd valueLimit populationBound : Nat) (objects : ι → TableFamily.Object) (writer reader blockReader recorder : ι)
    (protect : protectedCursor ≤ cursor)
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
    (outputArena : AllocatedBytes.Arena hashValue 32)
    (outputLocal : source.locals.lookup (ofString "h") = some (.val (.word hashValue)))
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
    (markerAbove : cutoff ≤ (transaction + 24#64).toNat) (markerBefore : (transaction + 24#64).toNat < protectedCursor)
    (markerOutside : TableFamily.Outside objects (transaction + 24#64)) (markerAway : Journal.Away base cap (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64)) (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerAbove : cutoff ≤ (transaction + 32#64).toNat) (outerBefore : (transaction + 32#64).toNat < protectedCursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < protectedCursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterBranch = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object)
      (nextEntries : Nat → Journal.Entry ι) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop) (nextCount : Nat),
      iterations ≤ populationBound + 3 ∧ AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
        (tailPrice populationBound destroyed found iterations) 3 (populationBound + iterations + 5) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "addr"] = some [.val (.word address)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressLocal]
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
  have oracle : ready.ffi.oracle = source.ffi.oracle := middleHash.hashCode.oracleEq.trans hashEnvironment.hashCode.oracleEq.symm
  have lookupPhase := AccountMutation.heap_prefix source ready cursor middleCursor cutoff protectedCursor (populationBound + 3) objects middleObjects outer base cap count entries accounts middleAccounts property
    prefixPaid (43 * populationBound + 31152) prefixFunded prefixClock prefixForward protect prefixPrice middleFamily middlePopulation image zone countBound journalAbove environment middleEnvironment
    prefixCode oracle prefixGlobals middleRegistry extension middleValues savedValues prefixFrame prefixMetadata counter
  have readyAddress : ready.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    rw [readyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "addr" by decide] using addressLocal
  have markerWord := lookupPhase.header_cell environment (transaction + 24#64) marker markerMapped markerStored markerAbove markerBefore markerOutside markerAway
  have outerWord := lookupPhase.header_cell environment (transaction + 32#64) outer outerMapped outerStored outerAbove outerBefore outerOutside outerAway
  have accountWord := lookupPhase.header_cell environment (transaction + 16#64) reader getMapped getCell accountAbove accountBefore accountOutside accountAway
  obtain ⟨answerEq,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,result⟩ := after_get_normal ready finish address account emptyHash hashValue scratch transaction
    middleCursor cutoff protectedCursor (populationBound + 3) middleObjects marker outer reader base cap count entries middlePopulation lookupPhase.family lookupPhase.image lookupPhase.zone countBound lookupPhase.environment middleInstalled
    middleAccounts lookupPhase.registry property lookupPhase.values markerOwned accountOwned lookupPhase.savedValues
    ((lookupPhase.metadata.kinds marker).trans markerKind) ((lookupPhase.metadata.kinds outer).trans outerKind) ((lookupPhase.metadata.kinds reader).trans readerKind) differentOuter addressArena scratchArena
    (fun index => Nat.le_trans world.ordered (middleFloors index)) keyScratchBelow (by have := world.ordered; have := world.bounded; omega) journalAbove member (Nat.le_trans protect prefixForward) readyAddress accountCell
    ((prefixGlobals (ofString "empty_code_hash") (by decide)).trans hashGlobal) hashArena outputArena (by rw [readyLocals]; simpa [HolFiniteMapExact.update,FUPDATE,show ofString "a" ≠ ofString "h" from by decide] using outputLocal) (lookupPhase.references references)
    ((prefixGlobals (ofString "sk_buf") (by decide)).trans scratchGlobal) ((prefixGlobals (ofString "ts") (by decide)).trans transactionGlobal)
    markerWord.1 markerWord.2.1 markerAbove markerAway markerBefore markerWord.2.2 outerWord.1 outerWord.2.1 outerBefore outerWord.2.2 outerAway
    accountWord.1 accountWord.2.1 accountAbove accountBefore accountWord.2.2 accountAway (extension.journal_apart accountApart zone.earlier)
    ((prefixGlobals (ofString "journal") (by decide)).trans journal) ((prefixGlobals (ofString "journal_cap") (by decide)).trans capacity) lookupPhase.counter returned tailRun
  have enlarged := result.relax (7 + AccountBalanceSet.commitPrice (populationBound + 3) (populationBound + 3) (populationBound + 3) destroyed found iterations) 3 (populationBound + iterations + 5)
    (Nat.add_le_add_left (AccountBalanceSet.commit_price_mono _ _ _ _ (middlePopulation marker) (middlePopulation outer) (middlePopulation reader) destroyed found iterations) 7) (Nat.le_refl _) (by omega)
  have combined := lookupPhase.trans enlarged
  refine ⟨answerEq,destroyed,found,iterations,nextCursor,next,nextEntries,middleAccounts ++ [BitVec.ofNat 64 middleCursor],AccountValueExtension.added property reader (BitVec.ofNat 64 middleCursor),nextCount,visits,?_⟩
  exact combined.local_agreement (by rw [scope]; rfl)

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.after_branch_normal
