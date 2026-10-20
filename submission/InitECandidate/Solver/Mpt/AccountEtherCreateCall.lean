import InitECandidate.Solver.Mpt.AccountEtherCreateNormal
import InitECandidate.Solver.Mpt.AccountEtherCreateEnvironment

namespace InitECandidate.Solver.Mpt.AccountEtherCreate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget AccountBalanceSet

theorem call_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions = some (AccountEtherCreate.values address words))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "create_ether") expressions) = (none,post)) :
    post.locals = source.locals ∧ Result source post cursor cutoff (populationBound + 3) objects reader base cap count accounts property
      (fun destroyed found iterations => 1 + wholePrice populationBound destroyed found iterations) := by
  obtain ⟨callee,called,addressLocal,amountLocal⟩ := AccountEtherCreate.environment source.code.lookup address words (original_code source.code installed)
  obtain ⟨positive,target,answer,bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "create_ether") expressions _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
  have entryWorld := world.of_agreement source entry ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)
  have entryHash := hashEnvironment.of_fields source entry stp pad rfl rfl rfl (HeapGlobals.refl source)
  have entryArena := arena.of_fields source entry scratchPtr limit rfl rfl
  have entryImage : Journal.Image entry objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨answerEq,result⟩ := whole_normal entry target transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit populationBound objects writer reader blockReader recorder
    entryFamily population writerKind readerKind blockReaderKind recorderKind (environment.of_fields rfl rfl rfl) installed accounts entryRegistry property tableValues writerOwned recorderOwned cacheKnown blockCacheKnown entryWorld afterWorld floors entryHash
    stateArena stateAligned padArena padAligned addressArena stateBelow padBelow entryArena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore
    setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell marker outer markerKind outerKind differentOuter markerOwned accountOwned references scratch scratchArena keyScratchBelow scratchGlobal
    base cap count entries entryImage zone countBound journalAbove savedValues accountApart markerMapped markerStored markerAbove markerBefore markerOutside markerAway outerMapped outerStored outerAbove outerBefore outerOutside outerAway
    accountAbove accountBefore accountOutside accountAway words addressLocal amountLocal journal capacity counter answer bodyRun
  rw [answerEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "create_ether") expressions _ body callee .one
    (.val (.word 0#64)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = {target with locals := source.locals} at postEq
  subst post
  have fullResult := result.prepend_mutation (source := source) 1 1 positive (Nat.le_refl _) rfl (Nat.le_refl _)
    (AccountDecode.Registry.Extension.refl accounts cursor) (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl)
    (TableFamily.Metadata.refl objects) (by intro name notHeap; rfl) rfl
  exact ⟨rfl,fullResult.locals source.locals⟩

end InitECandidate.Solver.Mpt.AccountEtherCreate

#print axioms InitECandidate.Solver.Mpt.AccountEtherCreate.call_normal
