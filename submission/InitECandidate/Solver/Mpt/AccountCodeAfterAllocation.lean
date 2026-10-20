import InitECandidate.Solver.Mpt.AccountCodeAfterHash
import InitECandidate.Solver.Mpt.AccountHashMutationResult

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_allocation_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit) (afterWorld : frozenEnd≤protectedCursor) (floors : ∀ index,frozenEnd≤(objects index).floor)
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
    (journalAfter : frozenEnd ≤ base)
    (setAbove : cutoff ≤ (transaction + 8#64).toNat) (setBefore : (transaction + 8#64).toNat < protectedCursor)
    (setOutside : TableFamily.Outside objects (transaction + 8#64)) (setAway : Journal.Away base cap (transaction + 8#64))
    (blockGetAbove : cutoff ≤ (block + 16#64).toNat) (blockGetBefore : (block + 16#64).toNat < protectedCursor)
    (blockGetOutside : TableFamily.Outside objects (block + 16#64)) (blockGetAway : Journal.Away base cap (block + 16#64))
    (recordAbove : cutoff ≤ (block + 72#64).toNat) (recordBefore : (block + 72#64).toNat < protectedCursor)
    (recordOutside : TableFamily.Outside objects (block + 72#64)) (recordAway : Journal.Away base cap (block + 72#64))
    (codeWriter : ι) (codeKind : (objects codeWriter).kind = .word) (code : BitVec 64) (length : Nat)
    (codeArena : AllocatedBytes.Arena code length)
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (codeMapped : source.memaddrs (transaction + 48#64)) (codeCell : source.memory (transaction + 48#64) = .word (objects codeWriter).pointer)
    (codeBefore : (transaction + 48#64).toNat < protectedCursor)
    (oldRegistry : AccountDecode.Registry source cutoff hashValue.toNat objects accounts)
    (outputAligned : hashValue.toNat % 8 = 0) (protectedOutput : protectedCursor ≤ hashValue.toNat) (outputBefore : hashValue.toNat ≤ cursor)
    (poolsBefore : ∀ index pool,(objects index).plan.base pool + size (objects index).kind (objects index).plan pool ≤ hashValue.toNat)
    (journalBefore : base + 32 * cap ≤ hashValue.toNat)
    (codeAbove : cutoff ≤ (transaction + 48#64).toNat) (codeOutside : TableFamily.Outside objects (transaction + 48#64)) (codeAway : Journal.Away base cap (transaction + 48#64))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterAllocation = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (created destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object)
      (nextEntries : Nat → Journal.Entry ι) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop) (nextCount : Nat),
      iterations ≤ populationBound + 4 ∧
      (if created then CodeSlice.Image post (BitVec.ofNat 64 cursor) code length else True) ∧
      AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
        (Keccak256.price length + 1 + (5 + (branchPrice (objects codeWriter).slots.length created + tailPrice (populationBound + 1) destroyed found iterations))) 4 (populationBound + iterations + 6) := by
  have safe : Input.LocalPrefix (ofString "addr") hashCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨ready,hashRun,tailRun,_⟩ := safe.normal_continue source post afterHash returned normal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "code",localVar "code_len",localVar "h"] = some (Keccak256.values code hashValue length) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,codeLocal,lengthLocal,outputLocal,Keccak256.values]
  have buffers : Keccak256.Buffers stp code pad hashValue length := ⟨stateArena,stateAligned,codeArena,padArena,padAligned,outputArena⟩
  obtain ⟨locals,first⟩ := AccountMutation.hash source ready cursor cutoff protectedCursor populationBound objects outer base cap count entries accounts property family image zone countBound population environment tableValues savedValues counter
    stp code pad hashValue length hashEnvironment buffers outputAligned stateBelow padBelow protectedOutput outputBefore (fun index => Nat.le_trans world.ordered (floors index)) poolsBefore oldRegistry journalAbove journalBefore _ args
    (WsAccountLeaf.hash_original_code source.code installed) hashRun
  obtain ⟨⟨readyWorld⟩,readyHash,readyArena,_,_⟩ := first.immutable_context ws root nibs stp pad scratchPtr limit frozenEnd valueLimit family world afterWorld floors journalAfter hashEnvironment arena
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [first.code]; exact installed
  have setter := first.header_cell environment (transaction + 8#64) writer setMapped setCell setAbove setBefore setOutside setAway
  have getter := first.header_cell environment (transaction + 16#64) reader getMapped getCell accountAbove accountBefore accountOutside accountAway
  have blockGetter := first.header_cell environment (block + 16#64) blockReader blockGetMapped blockGetCell blockGetAbove blockGetBefore blockGetOutside blockGetAway
  have recorded := first.header_cell environment (block + 72#64) recorder recordMapped recordCell recordAbove recordBefore recordOutside recordAway
  have marked := first.header_cell environment (transaction + 24#64) marker markerMapped markerStored markerAbove markerBefore markerOutside markerAway
  have outerCell := first.header_cell environment (transaction + 32#64) outer outerMapped outerStored outerAbove outerBefore outerOutside outerAway
  have codeWord := first.header_cell environment (transaction + 48#64) codeWriter codeMapped codeCell codeAbove codeBefore codeOutside codeAway
  obtain ⟨answerEq,created,destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,visits,sliceImage,second⟩ := after_hash_normal ready post
    transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash hashValue cursor cutoff protectedCursor frozenEnd valueLimit populationBound objects writer reader blockReader recorder protect
    first.family population writerKind readerKind blockReaderKind recorderKind first.environment readyInstalled accounts first.registry property first.values writerOwned recorderOwned cacheKnown blockCacheKnown readyWorld afterWorld floors readyHash
    stateArena stateAligned padArena padAligned addressArena stateBelow padBelow readyArena scratchBelow aligned sizeBound
    ((first.globals (ofString "empty_trie_root") (by decide) (by decide)).trans rootGlobal) ((first.globals (ofString "empty_code_hash") (by decide) (by decide)).trans hashGlobal) rootArena hashArena outputArena (by rw [locals]; exact outputLocal)
    ((first.globals (ofString "ts") (by decide) (by decide)).trans transactionGlobal) ((first.globals (ofString "bs") (by decide) (by decide)).trans blockGlobal) blockArena blockBefore transactionArena transactionBefore
    setter.1 setter.2.1 getter.1 getter.2.1 blockGetter.1 blockGetter.2.1 recorded.1 recorded.2.1 marker outer markerKind outerKind differentOuter markerOwned accountOwned references scratch scratchArena keyScratchBelow
    ((first.globals (ofString "sk_buf") (by decide) (by decide)).trans scratchGlobal) base cap count entries first.image zone countBound journalAbove first.savedValues accountApart marked.1 marked.2.1 markerAbove markerBefore marked.2.2 markerAway
    outerCell.1 outerCell.2.1 outerAbove outerBefore outerCell.2.2 outerAway accountAbove accountBefore getter.2.2 accountAway (by rw [locals]; exact addressLocal)
    ((first.globals (ofString "journal") (by decide) (by decide)).trans journal) ((first.globals (ofString "journal_cap") (by decide) (by decide)).trans capacity) first.counter journalAfter
    setAbove setBefore setter.2.2 setAway blockGetAbove blockGetBefore blockGetter.2.2 blockGetAway recordAbove recordBefore recorded.2.2 recordAway codeWriter codeKind code length codeArena
    (by rw [locals]; exact codeLocal) (by rw [locals]; exact lengthLocal) codeWord.1 codeWord.2.1 codeBefore returned tailRun
  exact ⟨answerEq,created,destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,visits,sliceImage,first.trans second⟩

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.after_allocation_normal
