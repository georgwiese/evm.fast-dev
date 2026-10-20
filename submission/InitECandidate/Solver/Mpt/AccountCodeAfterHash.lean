import InitECandidate.Solver.Mpt.AccountCodeAfterCompare
import InitECandidate.Solver.MutableTable.MemeqSmallNormalPrefix

namespace InitECandidate.Solver.Mpt.AccountCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_hash_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterHash = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (created destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object)
      (nextEntries : Nat → Journal.Entry ι) (nextAccounts : List (BitVec 64)) (nextProperty : ι → BitVec 64 → Prop) (nextCount : Nat),
      iterations ≤ populationBound + 4 ∧
      (if created then CodeSlice.Image post (BitVec.ofNat 64 cursor) code length else True) ∧
      AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts nextAccounts property nextProperty
        (5 + (branchPrice (objects codeWriter).slots.length created + tailPrice (populationBound + 1) destroyed found iterations)) 4 (populationBound + iterations + 6) := by
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [localVar "h",.var .global (ofString "empty_code_hash"),.const 32#64] = some (MemeqByteRuntime.values hashValue emptyHash 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,outputLocal,hashGlobal,MemeqByteRuntime.values]
  obtain ⟨paid,answer,finish,positive,price,funded,binary,tailRun,scope⟩ := MemeqSmall.normal_prefix source post hashValue emptyHash 32 (by decide)
    (by have := outputArena.upper; omega) (by have := hashArena.upper; omega)
    (fun offset inside => AllocatedBytes.byte_mapped source hashValue 32 offset environment.domain outputArena inside)
    (fun offset inside => AllocatedBytes.byte_mapped source emptyHash 32 offset environment.domain hashArena inside)
    environment.memeqCode "eq" _ afterCompare args returned normal
  let ready := bind {source with clock := source.clock - paid} "eq" answer
  have first := AccountMutation.control source cursor cutoff protectedCursor populationBound objects outer base cap count entries accounts property family image zone countBound protect population environment registry tableValues savedValues counter paid funded ready.locals
  have keep (name : String) (different : ofString "eq" ≠ ofString name) : ready.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have eqLocal : ready.locals.lookup (ofString "eq") = some (.val (.word answer)) := by simp [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨⟨readyWorld⟩,readyHash,readyArena,_,_⟩ := first.immutable_context ws root nibs stp pad scratchPtr limit frozenEnd valueLimit family world afterWorld floors journalAfter hashEnvironment arena
  obtain ⟨answerEq,created,destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,visits,sliceImage,second⟩ := after_compare_normal ready finish
    transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash hashValue cursor cutoff protectedCursor frozenEnd valueLimit populationBound objects writer reader blockReader recorder protect
    first.family population writerKind readerKind blockReaderKind recorderKind first.environment installed accounts first.registry property first.values writerOwned recorderOwned cacheKnown blockCacheKnown readyWorld afterWorld floors readyHash
    stateArena stateAligned padArena padAligned addressArena stateBelow padBelow readyArena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena outputArena ((keep "h" (by decide)).trans outputLocal)
    transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell marker outer markerKind outerKind differentOuter markerOwned accountOwned
    references scratch scratchArena keyScratchBelow scratchGlobal base cap count entries first.image zone countBound journalAbove first.savedValues accountApart markerMapped markerStored markerAbove markerBefore markerOutside markerAway
    outerMapped outerStored outerAbove outerBefore outerOutside outerAway accountAbove accountBefore accountOutside accountAway ((keep "addr" (by decide)).trans addressLocal) journal capacity counter journalAfter
    setAbove setBefore setOutside setAway blockGetAbove blockGetBefore blockGetOutside blockGetAway recordAbove recordBefore recordOutside recordAway codeWriter codeKind code length codeArena
    ((keep "code" (by decide)).trans codeLocal) ((keep "code_len" (by decide)).trans lengthLocal) codeMapped codeCell codeBefore answer eqLocal returned tailRun
  have finalSlice : if created then CodeSlice.Image post (BitVec.ofNat 64 cursor) code length else True := by
    cases created with
    | false => trivial
    | true => exact CodeSlice.Image.of_agreement finish post _ code length sliceImage (by rw [scope]; rfl) (by rw [scope]; rfl)
  have five : paid ≤ 5 := by change paid ≤ 4 + 1 at price; omega
  have combined := ((first.relax 5 0 populationBound five (Nat.le_refl _) (Nat.le_refl _)).trans second).local_agreement (post := post) (by rw [scope]; rfl)
  exact ⟨answerEq,created,destroyed,found,iterations,nextCursor,next,nextEntries,nextAccounts,nextProperty,nextCount,visits,finalSlice,combined⟩

end InitECandidate.Solver.Mpt.AccountCode

#print axioms InitECandidate.Solver.Mpt.AccountCode.after_hash_normal
