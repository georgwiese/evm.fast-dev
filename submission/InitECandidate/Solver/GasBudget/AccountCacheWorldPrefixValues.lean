import InitECandidate.Solver.GasBudget.AccountCachePrefixValues
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
theorem world_cache_prefix_values (kind : Kind) {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction readerRecord query ws root nibs stp pad scratchPtr limit : BitVec 64)
    (cursor cutoff frozenEnd valueLimit count : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤count)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
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
      Input.LocalEffects.erase post=Input.LocalEffects.erase inner ∧ post.clock=inner.clock ∧
      TableFamily.ValuesHave ready (Function.update objects writer next) property ∧ (flag=0#64 ∨ property reader value) ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source ready := by
  obtain ⟨paid,nextCursor,next,flag,value,ready,inner,funded,clock,amortized,nextKind,forward,countLower,countUpper,capacity,nextFamily,pointers,codeEq,oracleEq,nextEnvironment,globals,floorFrame,beforeWords,binary,queryCell,resultCell,tailRun,frame,postClock,nextValues,ownership,persistent⟩ :=
    outcome_cache_prefix_values (.returned returned) kind source post transaction readerRecord query cursor objects writer reader family writerKind readerKind environment installed property tableValues owned
      transactionGlobal readerGlobal recordBefore setMapped setCell getMapped getCell queryLocal (by have := queryArena.upper; omega)
      (fun offset active=>AllocatedBytes.byte_mapped source query 20 offset world.domain queryArena active) run
  have domain : ready.memaddrs=source.memaddrs := nextEnvironment.domain.trans environment.domain.symm
  have endian : ready.be=source.be := nextEnvironment.little.trans environment.little.symm
  let nextWorld := world.after_family source ready ws root nibs cutoff frozenEnd valueLimit objects (Function.update objects writer next) floorFrame floors domain endian globals
  have nextHashEnvironment := hashEnvironment.of_fields source ready stp pad domain codeEq oracleEq globals
  have nextArena := arena.of_heap_globals source ready scratchPtr limit domain globals
  have nextPopulation := TableFamily.population_update objects writer next count population countUpper
  have familyPrice := TableFamily.amortized_update objects writer next paid (9*(objects writer).slots.length+8*(Function.update objects writer next reader).slots.length+15)
    (by simpa only [TableFamily.Object.potential,writerKind,nextKind] using amortized)
  have price : paid+TableFamily.potential objects≤17*count+23+TableFamily.potential (Function.update objects writer next) := by
    have := population writer
    have := nextPopulation reader
    omega
  exact ⟨paid,nextCursor,next,flag,value,ready,inner,funded,clock,forward,nextKind,countLower,countUpper,capacity,nextFamily,nextPopulation,pointers,price,
    ⟨nextWorld⟩,nextHashEnvironment,nextArena,nextEnvironment,codeEq,globals,floorFrame,beforeWords,queryCell,resultCell,tailRun,frame,postClock,nextValues,ownership,persistent⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.world_cache_prefix_values
