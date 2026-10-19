import InitECandidate.Solver.GasBudget.AccountOptionalCallNormalValues
import InitECandidate.Solver.GasBudget.AccountOptionalNormal

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

set_option maxRecDepth 10000 in
/-- Genuine original transaction cache caller delivers the actual returned
word, retained ownership models and shared amortized price at its real
continuation. It derives all callee and future state models from execution. -/
theorem scoped_transaction_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit count : Nat) (objects : ι → TableFamily.Object) (writer reader blockReader recorder : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤count)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account) (blockReaderKind : (objects blockReader).kind=.account) (recorderKind : (objects recorder).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
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
    ∃ paid nextCursor nextObjects ready word inner,
      paid≤source.clock ∧ ready.clock=source.clock-paid ∧ cursor≤nextCursor ∧ TableFamily.Model ready nextCursor nextObjects ∧
      (∀ index,(nextObjects index).slots.length≤count+3) ∧ (∀ index,frozenEnd≤(nextObjects index).floor) ∧
      (∀ index,(nextObjects index).pointer=(objects index).pointer) ∧ Nonempty (WsAccountLeaf.World ready ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment ready stp pad ∧ Rlp.Validation.Arena ready scratchPtr limit ∧ HeapGlobals source ready ∧ ready.code=source.code ∧
      paid+TableFamily.potential objects≤43*count+31148+TableFamily.potential nextObjects ∧
      ready.locals.lookup (ofString name)=some (.val (.word word)) ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨paid,nextCursor,nextObjects,nextAccounts,ready,word,inner,funded,clock,forward,nextFamily,nextPopulation,nextFloors,pointers,nextWorld,nextHash,nextArena,globals,codeEq,price,_,_,_,_,resultCell,tailRun,restored⟩ :=
    scoped_transaction_normal_values source post transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit count objects writer reader blockReader recorder
      family population writerKind readerKind blockReaderKind recorderKind environment installed [] (AccountDecode.Registry.empty source cutoff cursor objects)
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro True.intro world afterWorld floors hashEnvironment stateArena stateAligned padArena padAligned queryArena stateBelow padBelow
      arena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore transactionArena transactionBefore setMapped setCell getMapped getCell blockGetMapped blockGetCell recordMapped recordCell
      name arguments continuation args returned normal
  exact ⟨paid,nextCursor,nextObjects,ready,word,inner,funded,clock,forward,nextFamily,nextPopulation,nextFloors,pointers,nextWorld,nextHash,nextArena,globals,codeEq,price,resultCell,tailRun,restored⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.scoped_transaction_normal
