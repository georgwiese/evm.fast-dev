import InitECandidate.Solver.GasBudget.AccountOptionalNormalValues

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

set_option maxRecDepth 10000 in
/-- Genuine original transaction cache caller delivers the actual returned
word, retained ownership models and shared amortized price at its real
continuation. It derives all callee and future state models from execution. -/
theorem scoped_transaction_normal_values {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit count : Nat) (objects : ι → TableFamily.Object) (writer reader blockReader recorder : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤count)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account) (blockReaderKind : (objects blockReader).kind=.account) (recorderKind : (objects recorder).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
    (writerOwned : property writer 1#64) (recorderOwned : property recorder 1#64)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit) (afterWorld : frozenEnd≤cursor) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (hashEnvironment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0) (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0)
    (queryArena : AllocatedBytes.Arena query 20) (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
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
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word query)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "get_account_optional") arguments continuation)=(some (.returned returned),post)) :
    ∃ paid nextCursor nextObjects nextAccounts ready word inner,
      paid≤source.clock ∧ ready.clock=source.clock-paid ∧ cursor≤nextCursor ∧ TableFamily.Model ready nextCursor nextObjects ∧
      (∀ index,(nextObjects index).slots.length≤count+3) ∧ (∀ index,frozenEnd≤(nextObjects index).floor) ∧
      (∀ index,(nextObjects index).pointer=(objects index).pointer) ∧ Nonempty (WsAccountLeaf.World ready ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment ready stp pad ∧ Rlp.Validation.Arena ready scratchPtr limit ∧ HeapGlobals source ready ∧ ready.code=source.code ∧
      paid+TableFamily.potential objects≤43*count+31148+TableFamily.potential nextObjects ∧
      AccountDecode.Registry ready cutoff nextCursor nextObjects nextAccounts ∧ TableFamily.ValuesHave ready nextObjects property ∧
      AccountDecode.Registry.Extension accounts nextAccounts cursor ∧
      (property reader word ∨ property blockReader word ∨ AccountDecode.Registry.Known nextAccounts word) ∧
      ready.locals.lookup (ofString name)=some (.val (.word word)) ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,queryCell⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "get_account_optional") "addr" Kind.transaction.body query
    (Kind.transaction.original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one
    (ofString "get_account_optional") arguments _ Kind.transaction.body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  let entryWorld := world.of_agreement source entry ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)
  have entryHash := hashEnvironment.of_fields source entry stp pad rfl rfl rfl (HeapGlobals.refl source)
  have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
  have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
  obtain ⟨bodyPaid,nextCursor,nextObjects,nextAccounts,funded,clock,forward,nextFamily,nextPopulation,nextFloors,pointers,⟨targetWorld⟩,targetHash,targetArena,globals,codeEq,price,nextRegistry,nextValues,weakening,word,answerEq,ownership⟩ :=
    transaction_body_normal_values entry target transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit count objects writer reader blockReader recorder
      entryFamily population writerKind readerKind blockReaderKind recorderKind (environment.of_fields rfl rfl rfl) installed accounts entryRegistry property tableValues writerOwned recorderOwned entryWorld afterWorld floors entryHash
      stateArena stateAligned padArena padAligned queryArena stateBelow padBelow (arena.of_fields source entry scratchPtr limit rfl rfl) scratchBelow aligned sizeBound
      rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell queryCell answer bodyRun
  rw [answerEq] at tailRun
  let ready := Input.CallNormal.continuationEntry source target name (.val (.word word))
  let readyWorld := targetWorld.of_agreement target ready ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)
  have readyHash := targetHash.of_fields target ready stp pad rfl rfl rfl (HeapGlobals.refl target)
  have readyFamily : TableFamily.Model ready nextCursor nextObjects := nextFamily.of_control rfl rfl rfl rfl
  have readyArena := targetArena.of_fields target ready scratchPtr limit rfl rfl
  have readyRegistry := nextRegistry.framed target ready cutoff nextCursor nextCursor nextObjects nextObjects nextAccounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor nextObjects target ready rfl) (Nat.le_refl _) rfl
  have readyValues := nextValues.of_memory target ready nextObjects property rfl
  change bodyPaid≤source.clock-1 at funded
  change target.clock=source.clock-1-bodyPaid at clock
  let paid := bodyPaid+1
  have paidFits : paid≤source.clock := by dsimp [paid]; omega
  have readyClock : ready.clock=source.clock-paid := by change target.clock=source.clock-paid; dsimp [paid]; omega
  exact ⟨paid,nextCursor,nextObjects,nextAccounts,ready,word,inner,paidFits,readyClock,forward,readyFamily,nextPopulation,nextFloors,pointers,
    ⟨readyWorld⟩,readyHash,readyArena,globals,codeEq,(by dsimp [paid]; omega),readyRegistry,readyValues,weakening,ownership,
    Input.CallNormal.continuation_lookup_same source target name (.val (.word word)),tailRun,restored⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.scoped_transaction_normal_values
