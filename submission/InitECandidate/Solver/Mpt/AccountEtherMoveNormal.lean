import InitECandidate.Solver.Mpt.AccountEtherMoveSenderPrefix
import InitECandidate.Solver.Mpt.AccountEtherMoveRecipientNormal
import InitECandidate.Solver.Mpt.AccountMutationImmutableContext
import InitECandidate.Solver.Mpt.AccountMutationBalanceResult
import InitECandidate.Solver.Mpt.AccountMutationAgreement

namespace InitECandidate.Solver.Mpt.AccountEtherMove
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
    (words : Input.RlpWrite.U256Value.Words)
    (addressLocal : source.locals.lookup (ofString "sender") = some (.val (.word address)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple words))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (recipientAddress : BitVec 64) (recipientArena : AllocatedBytes.Arena recipientAddress 20)
    (recipientLocal : source.locals.lookup (ofString "recipient") = some (.val (.word recipientAddress)))
    (journalAfter : frozenEnd ≤ base)
    (setAbove : cutoff ≤ (transaction + 8#64).toNat) (setBefore : (transaction + 8#64).toNat < cursor)
    (setOutside : TableFamily.Outside objects (transaction + 8#64)) (setAway : Journal.Away base cap (transaction + 8#64))
    (blockGetAbove : cutoff ≤ (block + 16#64).toNat) (blockGetBefore : (block + 16#64).toNat < cursor)
    (blockGetOutside : TableFamily.Outside objects (block + 16#64)) (blockGetAway : Journal.Away base cap (block + 16#64))
    (recordAbove : cutoff ≤ (block + 72#64).toNat) (recordBefore : (block + 72#64).toNat < cursor)
    (recordOutside : TableFamily.Outside objects (block + 72#64)) (recordAway : Journal.Away base cap (block + 72#64))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧
    ∃ (destroyedSender foundSender : Bool) (senderIterations : Nat) (destroyedRecipient foundRecipient : Bool) (recipientIterations nextCursor : Nat)
      (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop) (nextCount : Nat),
      senderIterations ≤ populationBound + 3 ∧ recipientIterations ≤ receiverPopulation populationBound senderIterations + 3 ∧
      AccountMutation.Result source post cursor nextCursor cutoff cursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
        (wholePrice populationBound destroyedSender foundSender senderIterations destroyedRecipient foundRecipient recipientIterations) 6
        (populationBound + senderIterations + recipientIterations + 10) := by
  obtain ⟨middle,finish,copyCursor,middleAccounts,newNb,destroyedSender,foundSender,senderIterations,middleCursor,middleObjects,middleEntries,middleCount,copyForward,senderVisits,keepRecipient,middleAmount,middleNb,first,recipientRun,postFrame⟩ := sender_prefix source post
    transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit populationBound objects writer reader blockReader recorder family population writerKind readerKind blockReaderKind recorderKind
    environment installed accounts registry property tableValues writerOwned recorderOwned cacheKnown blockCacheKnown world afterWorld floors hashEnvironment stateArena stateAligned padArena padAligned addressArena stateBelow padBelow arena scratchBelow aligned sizeBound
    rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell marker outer markerKind outerKind differentOuter markerOwned accountOwned
    references scratch scratchArena keyScratchBelow scratchGlobal base cap count entries image zone countBound journalAbove savedValues accountApart markerMapped markerStored markerAbove markerBefore markerOutside markerAway outerMapped outerStored outerAbove outerBefore outerOutside outerAway
    accountAbove accountBefore accountOutside accountAway words addressLocal amountLocal journal capacity counter returned normal
  obtain ⟨⟨middleWorld⟩,middleHash,middleArena,middleAfter,middleFloors⟩ := first.immutable_context ws root nibs stp pad scratchPtr limit frozenEnd valueLimit family world afterWorld floors journalAfter hashEnvironment arena
  have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [first.code]; exact installed
  have setter := first.header_cell environment (transaction + 8#64) writer setMapped setCell setAbove setBefore setOutside setAway
  have getter := first.header_cell environment (transaction + 16#64) reader getMapped getCell accountAbove accountBefore accountOutside accountAway
  have blockGetter := first.header_cell environment (block + 16#64) blockReader blockGetMapped blockGetCell blockGetAbove blockGetBefore blockGetOutside blockGetAway
  have recorded := first.header_cell environment (block + 72#64) recorder recordMapped recordCell recordAbove recordBefore recordOutside recordAway
  have marked := first.header_cell environment (transaction + 24#64) marker markerMapped markerStored markerAbove markerBefore markerOutside markerAway
  have outerCell := first.header_cell environment (transaction + 32#64) outer outerMapped outerStored outerAbove outerBefore outerOutside outerAway
  have middleBlockBefore : block.toNat + 80 ≤ (middleObjects writer).floor := by rw [first.metadata.floors writer]; exact blockBefore
  have middleTransactionBefore : transaction.toNat + 72 ≤ (middleObjects writer).floor := by rw [first.metadata.floors writer]; exact transactionBefore
  obtain ⟨answerEq,secondResult⟩ := recipient_normal middle finish transaction block recipientAddress ws root nibs stp pad scratchPtr limit emptyRoot emptyHash middleCursor cutoff frozenEnd valueLimit
    (receiverPopulation populationBound senderIterations) middleObjects writer reader blockReader recorder first.family first.populations
    ((first.metadata.kinds writer).trans writerKind) ((first.metadata.kinds reader).trans readerKind) ((first.metadata.kinds blockReader).trans blockReaderKind) ((first.metadata.kinds recorder).trans recorderKind)
    first.environment middleInstalled middleAccounts first.registry (AccountValueExtension.added property reader (BitVec.ofNat 64 copyCursor)) first.values
    (first.propertyIncluded writer 1#64 writerOwned) (first.propertyIncluded recorder 1#64 recorderOwned) (first.readerKnown reader readerKind cacheKnown) (first.readerKnown blockReader blockReaderKind blockCacheKnown)
    middleWorld middleAfter middleFloors middleHash stateArena stateAligned padArena padAligned recipientArena stateBelow padBelow middleArena scratchBelow aligned sizeBound
    ((first.globals (ofString "empty_trie_root") (by decide) (by decide)).trans rootGlobal) ((first.globals (ofString "empty_code_hash") (by decide) (by decide)).trans hashGlobal) rootArena hashArena
    ((first.globals (ofString "ts") (by decide) (by decide)).trans transactionGlobal) ((first.globals (ofString "bs") (by decide) (by decide)).trans blockGlobal) blockArena middleBlockBefore transactionArena middleTransactionBefore
    setter.1 setter.2.1 getter.1 getter.2.1 blockGetter.1 blockGetter.2.1 recorded.1 recorded.2.1 marker outer ((first.metadata.kinds marker).trans markerKind) ((first.metadata.kinds outer).trans outerKind)
    differentOuter (first.propertyIncluded marker 1#64 markerOwned) (first.propertyIncluded reader 1#64 accountOwned) (first.references references) scratch scratchArena keyScratchBelow
    ((first.globals (ofString "sk_buf") (by decide) (by decide)).trans scratchGlobal) base cap middleCount middleEntries first.image first.zone first.countBound journalAbove first.savedValues
    (first.extension.journal_apart accountApart zone.earlier) marked.1 marked.2.1 markerAbove (by have := first.cursorForward; omega) marked.2.2 markerAway outerCell.1 outerCell.2.1 outerAbove
    (by have := first.cursorForward; omega) outerCell.2.2 outerAway accountAbove (by have := first.cursorForward; omega) getter.2.2 accountAway words newNb (keepRecipient.trans recipientLocal) middleAmount middleNb
    ((first.globals (ofString "journal") (by decide) (by decide)).trans journal) ((first.globals (ofString "journal_cap") (by decide) (by decide)).trans capacity) first.counter returned recipientRun
  have oracle := Input.evaluation_oracle middle finish recipient (some (.returned returned)) recipientRun
  obtain ⟨destroyedRecipient,foundRecipient,recipientIterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,recipientVisits,second⟩ :=
    AccountMutation.of_balance oracle differentOuter first.cursorForward secondResult
  have combined := (first.trans second).local_agreement postFrame
  refine ⟨answerEq,destroyedSender,foundSender,senderIterations,destroyedRecipient,foundRecipient,recipientIterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,senderVisits,recipientVisits,?_⟩
  exact combined.relax _ 6 (populationBound + senderIterations + recipientIterations + 10) (Nat.le_refl _) (Nat.le_refl _) (by unfold receiverPopulation; omega)

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.whole_normal
