import InitECandidate.Solver.Mpt.StorageSetNormal
import InitECandidate.Solver.Mpt.StorageSetEnvironment

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem call_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 journalCount))))
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions = some (StorageSet.values address key words))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "set_storage") expressions) = (none,post)) :
    post.locals = source.locals ∧ ∃ nextAccounts,AccountDecode.Registry.Extension accounts nextAccounts cursor ∧
      Result source post cursor cutoff (populationBound + 3) objects outer base cap journalCount nextAccounts property (fun created => 1 + wholePrice populationBound created) := by
  obtain ⟨callee,called,addressLocal,keyLocal,valueLocal⟩ := StorageSet.environment source.code.lookup address key words (original_code source.code installed)
  obtain ⟨positive,target,answer,bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "set_storage") expressions _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
  have entryWorld := world.of_agreement source entry ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)
  have entryHash := hashEnvironment.of_fields source entry stp pad rfl rfl rfl (HeapGlobals.refl source)
  have entryArena := arena.of_fields source entry scratchPtr limit rfl rfl
  have entryImage : Journal.Image entry objects base journalCount entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  obtain ⟨answerEq,nextAccounts,extension,result⟩ := whole_normal entry target transaction block address ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit populationBound objects writer reader blockReader recorder
    entryFamily population writerKind readerKind blockReaderKind recorderKind (environment.of_fields rfl rfl rfl) installed accounts entryRegistry property tableValues writerOwned recorderOwned entryWorld afterWorld floors entryHash
    stateArena stateAligned padArena padAligned addressArena stateBelow padBelow entryArena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore
    setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell key words keyArena outer outerKind references freshOwned base cap journalCount entries entryImage zone countBound journalAbove savedValues accountApart
    storageMapped storageStored storageAbove storageBefore storageOutside addressLocal keyLocal valueLocal journal capacity counter answer bodyRun
  rw [answerEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "set_storage") expressions _ body callee .one
    (.val (.word 0#64)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = {target with locals := source.locals} at postEq
  subst post
  have fullResult := result.prepend_readonly (source := source) 1 1 positive (Nat.le_refl _) rfl rfl rfl rfl
  exact ⟨rfl,nextAccounts,extension,fullResult.locals source.locals⟩

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.call_normal
