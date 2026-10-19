import InitECandidate.Solver.GasBudget.AccountCacheWorldPrefixValues
import InitECandidate.Solver.GasBudget.AccountCachePrefix
import InitECandidate.Solver.Mpt.WsAccountWorldAgreement
import InitECandidate.Solver.WitnessRadix.Keccak256EnvironmentFields
import InitECandidate.Solver.Rlp.ValidationHeapGlobals
import InitECandidate.Solver.MutableTable.FamilyPotential

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

/-- Original cache prefix transports current witness/hash/scratch ownership
through its actual touched-set growth and getter, and charges the complete
live family's potential. No future cache or provider model is a premise. -/
theorem world_cache_prefix (kind : Kind) {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction readerRecord query ws root nibs stp pad scratchPtr limit : BitVec 64)
    (cursor cutoff frozenEnd valueLimit count : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤count)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (hashEnvironment : Keccak256.Environment source stp pad) (arena : Rlp.Validation.Arena source scratchPtr limit) (queryArena : AllocatedBytes.Arena query 20)
    (transactionGlobal : source.globals.lookup (ofString "ts")=some (.val (.word transaction)))
    (readerGlobal : source.globals.lookup (ofString kind.readerGlobal)=some (.val (.word readerRecord)))
    (recordBefore : readerRecord.toNat+72≤(objects writer).floor)
    (setMapped : source.memaddrs (transaction+8#64)) (setCell : source.memory (transaction+8#64)=.word (objects writer).pointer)
    (getMapped : source.memaddrs (readerRecord+16#64)) (getCell : source.memory (readerRecord+16#64)=.word (objects reader).pointer)
    (queryLocal : source.locals.lookup (ofString "addr")=some (.val (.word query)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source kind.body=(some (.returned returned),post)) :
    ∃ paid nextCursor next flag value ready inner,
      paid≤source.clock ∧ ready.clock=source.clock-paid ∧ cursor≤nextCursor ∧ next.kind=.account ∧
      (objects writer).slots.length≤next.slots.length ∧ next.slots.length≤(objects writer).slots.length+1 ∧
      next.plan.capacity≤max (objects writer).plan.capacity (4*(next.slots.length+1)) ∧
      TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index,(Function.update objects writer next index).slots.length≤count+1) ∧
      (∀ index,(Function.update objects writer next index).pointer=(objects index).pointer) ∧
      paid+TableFamily.potential objects≤17*count+23+TableFamily.potential (Function.update objects writer next) ∧
      Nonempty (WsAccountLeaf.World ready ws root nibs cutoff frozenEnd valueLimit) ∧ Keccak256.Environment ready stp pad ∧
      Rlp.Validation.Arena ready scratchPtr limit ∧ WarmKeys.Environment ready ∧ ready.code=source.code ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      (∀ address : BitVec 64,address.toNat<(objects writer).floor → ready.memory address=source.memory address) ∧
      ready.locals.lookup (ofString "addr")=some (.val (.word query)) ∧ ready.locals.lookup (ofString "w")=some (Get.pair flag value) ∧
      evaluateHOLFiniteState ready kind.afterGet=(some (.returned returned),inner) ∧
      Input.LocalEffects.erase post=Input.LocalEffects.erase inner ∧ post.clock=inner.clock := by
  obtain ⟨paid,nextCursor,next,flag,value,ready,inner,funded,clock,forward,nextKind,countLower,countUpper,capacity,nextFamily,nextPopulation,pointers,price,nextWorld,nextHash,nextArena,nextEnvironment,codeEq,globals,floorFrame,beforeWords,queryCell,resultCell,tailRun,frame,postClock,_,_,_⟩ :=
    world_cache_prefix_values kind source post transaction readerRecord query ws root nibs stp pad scratchPtr limit cursor cutoff frozenEnd valueLimit count objects writer reader
      family population writerKind readerKind environment installed (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro world floors hashEnvironment arena queryArena
      transactionGlobal readerGlobal recordBefore setMapped setCell getMapped getCell queryLocal returned run
  exact ⟨paid,nextCursor,next,flag,value,ready,inner,funded,clock,forward,nextKind,countLower,countUpper,capacity,nextFamily,nextPopulation,pointers,price,nextWorld,nextHash,nextArena,nextEnvironment,codeEq,globals,floorFrame,beforeWords,queryCell,resultCell,tailRun,frame,postClock⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.world_cache_prefix
