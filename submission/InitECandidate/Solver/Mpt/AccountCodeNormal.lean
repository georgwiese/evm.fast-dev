import InitECandidate.Solver.Mpt.AccountCodeAfterAllocation

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

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
    (journalAfter : frozenEnd ≤ base)
    (setAbove : cutoff ≤ (transaction + 8#64).toNat) (setBefore : (transaction + 8#64).toNat < cursor)
    (setOutside : TableFamily.Outside objects (transaction + 8#64)) (setAway : Journal.Away base cap (transaction + 8#64))
    (blockGetAbove : cutoff ≤ (block + 16#64).toNat) (blockGetBefore : (block + 16#64).toNat < cursor)
    (blockGetOutside : TableFamily.Outside objects (block + 16#64)) (blockGetAway : Journal.Away base cap (block + 16#64))
    (recordAbove : cutoff ≤ (block + 72#64).toNat) (recordBefore : (block + 72#64).toNat < cursor)
    (recordOutside : TableFamily.Outside objects (block + 72#64)) (recordAway : Journal.Away base cap (block + 72#64))
    (codeWriter : ι) (codeKind : (objects codeWriter).kind = .word) (code : BitVec 64) (length : Nat)
    (codeArena : AllocatedBytes.Arena code length)
    (codeLocal : source.locals.lookup (ofString "code") = some (.val (.word code)))
    (lengthLocal : source.locals.lookup (ofString "code_len") = some (.val (.word (BitVec.ofNat 64 length))))
    (codeMapped : source.memaddrs (transaction + 48#64)) (codeCell : source.memory (transaction + 48#64) = .word (objects codeWriter).pointer)
    (codeBefore : (transaction + 48#64).toNat < cursor)
    (codeAbove : cutoff ≤ (transaction + 48#64).toNat) (codeOutside : TableFamily.Outside objects (transaction + 48#64)) (codeAway : Journal.Away base cap (transaction + 48#64))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (created destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object)
      (nextEntries : Nat → Journal.Entry ι) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop) (nextCount : Nat),
      iterations ≤ populationBound + 4 ∧
      (if created then CodeSlice.Image post (BitVec.ofNat 64 (cursor + 32)) code length else True) ∧
      AccountMutation.Result source post cursor nextCursor cutoff cursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
        (1 + (Keccak256.price length + 1 + (5 + (branchPrice (objects codeWriter).slots.length created + tailPrice (populationBound + 1) destroyed found iterations)))) 4 (populationBound + iterations + 6) := by
  rw [body_shape] at normal
  obtain ⟨room,funded,outputArena,outputAligned,first,finish,tailRun,scope⟩ := AccountMutation.allocate source post cursor cutoff cursor populationBound objects writer outer base cap count entries accounts property family image zone countBound
    (Nat.le_refl _) journalAbove population environment registry tableValues savedValues counter "h" 32 (by decide) (by decide) afterAllocation returned normal
  let ready := PersistentAlloc.nextState source "h" cursor (cursor + 32)
  let heap := BitVec.ofNat 64 cursor
  have heapNumber : heap.toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := (family.tables writer).bounded; omega)]
  have keep (name : String) (different : ofString "h" ≠ ofString name) : ready.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    simp [ready,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have hashLocal : ready.locals.lookup (ofString "h") = some (.val (.word heap)) := by
    simp [ready,heap,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have oldFrame : TableFamily.PersistentFrame cutoff cursor objects objects source ready := TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl
  have oldRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts oldFrame (Nat.le_refl _) rfl
  obtain ⟨⟨readyWorld⟩,readyHash,readyArena,_,_⟩ := first.immutable_context ws root nibs stp pad scratchPtr limit frozenEnd valueLimit family world afterWorld floors journalAfter hashEnvironment arena
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [first.code]; exact installed
  obtain ⟨answerEq,created,destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,visits,sliceImage,second⟩ := after_allocation_normal ready finish
    transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash heap (cursor + 32) cutoff cursor frozenEnd valueLimit populationBound objects writer reader blockReader recorder (by omega)
    first.family population writerKind readerKind blockReaderKind recorderKind first.environment readyInstalled accounts first.registry property first.values writerOwned recorderOwned cacheKnown blockCacheKnown readyWorld afterWorld floors readyHash
    stateArena stateAligned padArena padAligned addressArena stateBelow padBelow readyArena scratchBelow aligned sizeBound
    ((first.globals (ofString "empty_trie_root") (by decide) (by decide)).trans rootGlobal) ((first.globals (ofString "empty_code_hash") (by decide) (by decide)).trans hashGlobal) rootArena hashArena outputArena hashLocal
    ((first.globals (ofString "ts") (by decide) (by decide)).trans transactionGlobal) ((first.globals (ofString "bs") (by decide) (by decide)).trans blockGlobal) blockArena blockBefore transactionArena transactionBefore
    setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell marker outer markerKind outerKind differentOuter markerOwned accountOwned references scratch scratchArena keyScratchBelow
    ((first.globals (ofString "sk_buf") (by decide) (by decide)).trans scratchGlobal) base cap count entries first.image first.zone countBound journalAbove first.savedValues accountApart markerMapped markerStored markerAbove markerBefore markerOutside markerAway
    outerMapped outerStored outerAbove outerBefore outerOutside outerAway accountAbove accountBefore accountOutside accountAway ((keep "addr" (by decide)).trans addressLocal)
    ((first.globals (ofString "journal") (by decide) (by decide)).trans journal) ((first.globals (ofString "journal_cap") (by decide) (by decide)).trans capacity) first.counter journalAfter
    setAbove setBefore setOutside setAway blockGetAbove blockGetBefore blockGetOutside blockGetAway recordAbove recordBefore recordOutside recordAway codeWriter codeKind code length codeArena
    ((keep "code" (by decide)).trans codeLocal) ((keep "code_len" (by decide)).trans lengthLocal) codeMapped codeCell codeBefore
    (by rw [heapNumber]; exact oldRegistry) outputAligned (by rw [heapNumber]) (by rw [heapNumber]; omega)
    (by intro index pool; rw [heapNumber]; exact (family.tables index).earlier pool) (by rw [heapNumber]; exact zone.earlier) codeAbove codeOutside codeAway returned tailRun
  have finalSlice : if created then CodeSlice.Image post (BitVec.ofNat 64 (cursor + 32)) code length else True := by
    cases created with
    | false => trivial
    | true => exact CodeSlice.Image.of_agreement finish post _ code length sliceImage (by rw [scope]; rfl) (by rw [scope]; rfl)
  have combined := (first.trans second).local_agreement (post := post) (by rw [scope]; rfl)
  exact ⟨answerEq,created,destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,visits,finalSlice,combined⟩

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.whole_normal
