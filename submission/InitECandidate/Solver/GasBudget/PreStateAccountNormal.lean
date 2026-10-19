import InitECandidate.Solver.GasBudget.AccountCacheWorldPrefix
import InitECandidate.Solver.GasBudget.AccountCacheDispatch
import InitECandidate.Solver.GasBudget.PreStateAccountMissComplete

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

/-- Complete original get_pre_state_account_optional normal execution,
including cache hits and actual recorded/provider misses. Shared family
potential accounts for both writers. This proves runtime/current ownership;
ownership of values retrieved on cache hits is a separate invariant. -/
theorem pre_state_body_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit count : Nat) (objects : ι → TableFamily.Object) (writer reader recorder : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤count)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account) (recorderKind : (objects recorder).kind=.account)
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
    (setMapped : source.memaddrs (transaction+8#64)) (setCell : source.memory (transaction+8#64)=.word (objects writer).pointer)
    (getMapped : source.memaddrs (block+16#64)) (getCell : source.memory (block+16#64)=.word (objects reader).pointer)
    (recordMapped : source.memaddrs (block+72#64)) (recordCell : source.memory (block+72#64)=.word (objects recorder).pointer)
    (queryLocal : source.locals.lookup (ofString "addr")=some (.val (.word query)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source Kind.preState.body=(some (.returned returned),post)) :
    ∃ paid nextCursor nextObjects,paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤nextCursor ∧ TableFamily.Model post nextCursor nextObjects ∧
      (∀ index,(nextObjects index).slots.length≤count+2) ∧ (∀ index,frozenEnd≤(nextObjects index).floor) ∧
      (∀ index,(nextObjects index).pointer=(objects index).pointer) ∧ Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment post stp pad ∧ Rlp.Validation.Arena post scratchPtr limit ∧ HeapGlobals source post ∧ post.code=source.code ∧
      paid+TableFamily.potential objects≤26*count+31097+TableFamily.potential nextObjects ∧ ∃ value : BitVec 64,returned=.val (.word value) := by
  obtain ⟨prefixPaid,prefixCursor,next,flag,value,ready,inner,funded,prefixClock,forward,nextKind,countLower,countUpper,capacity,prefixFamily,prefixPopulation,pointers,prefixPrice,⟨currentWorld⟩,currentHash,currentArena,currentEnvironment,codeEq,prefixGlobals,floorFrame,beforeWords,queryCell,resultCell,tailRun,frame,postClock⟩ :=
    world_cache_prefix .preState source post transaction block query ws root nibs stp pad scratchPtr limit cursor cutoff frozenEnd valueLimit count objects writer reader
      family population writerKind readerKind environment installed world floors hashEnvironment arena queryArena transactionGlobal blockGlobal
      (by omega) setMapped setCell getMapped getCell queryLocal returned run
  let current := Function.update objects writer next
  change ∀ index,(current index).slots.length≤count+1 at prefixPopulation
  change prefixPaid+TableFamily.potential objects≤17*count+23+TableFamily.potential current at prefixPrice
  have currentFloors : ∀ index,frozenEnd≤(current index).floor := by intro index; rw [floorFrame.floors index]; exact floors index
  have currentKind : (current recorder).kind=.account := by
    by_cases same : recorder=writer
    · subst recorder; simpa only [current,Function.update_self] using nextKind
    · simpa only [current,Function.update_of_ne same] using recorderKind
  have tail : ∃ finalCursor finalObjects,prefixCursor≤finalCursor ∧ TableFamily.Model inner finalCursor finalObjects ∧
      (∀ index,(finalObjects index).slots.length≤count+2) ∧ (∀ index,frozenEnd≤(finalObjects index).floor) ∧
      (∀ index,(finalObjects index).pointer=(current index).pointer) ∧ Nonempty (WsAccountLeaf.World inner ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment inner stp pad ∧ Rlp.Validation.Arena inner scratchPtr limit ∧ HeapGlobals ready inner ∧
      ready.clock-inner.clock+TableFamily.potential current≤9*count+31074+TableFamily.potential finalObjects ∧ ∃ word : BitVec 64,returned=.val (.word word) := by
    rw [cache_dispatch .preState ready flag value resultCell] at tailRun
    by_cases zero : flag=0#64
    · rw [if_pos zero] at tailRun
      have domain : ready.memaddrs=source.memaddrs := currentEnvironment.domain.trans environment.domain.symm
      have currentMapped : ready.memaddrs (block+72#64) := by rw [domain]; exact recordMapped
      have number : (block+72#64).toNat=block.toNat+72 := BitVec.toNat_add_of_lt (by change block.toNat+72<2^64; have := blockArena.upper; omega)
      have currentStored : ready.memory (block+72#64)=.word (current recorder).pointer := by
        rw [beforeWords _ (by rw [number]; omega),recordCell]
        rw [pointers recorder]
      obtain ⟨paid,recordCursor,readNext,finalCursor,paidFits,clock,more,readKind,choice,finalFamily,stable,floorStable,price,lower,upper,cap,finalWorld,finalHash,result,globals,codes,image⟩ :=
        pre_state_miss_complete ready inner block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash prefixCursor cutoff frozenEnd valueLimit current recorder
          prefixFamily currentKind currentEnvironment (by rw [codeEq]; exact installed) currentWorld (by omega) currentFloors currentHash
          stateArena stateAligned padArena padAligned queryArena stateBelow padBelow currentArena scratchBelow aligned sizeBound
          ((prefixGlobals _ (by decide)).trans rootGlobal) ((prefixGlobals _ (by decide)).trans hashGlobal) rootArena hashArena
          ((prefixGlobals _ (by decide)).trans blockGlobal) currentMapped currentStored queryCell returned tailRun
      have nextPopulation := TableFamily.population_update current recorder readNext (count+1) prefixPopulation upper
      have familyPrice := TableFamily.amortized_update current recorder readNext paid (9*(current recorder).slots.length+31065)
        (by simpa only [TableFamily.Object.potential,currentKind,readKind] using price)
      have paidEq : ready.clock-inner.clock=paid := by omega
      refine ⟨finalCursor,Function.update current recorder readNext,by rcases choice with choice | choice <;> omega,finalFamily,nextPopulation,?_,stable,
        finalWorld,finalHash,result.1,globals,?_,?_⟩
      · intro index; rw [floorStable index]; exact currentFloors index
      · rw [paidEq]; have := prefixPopulation recorder; omega
      · rcases result.2 with absent | present
        · exact ⟨1#64,absent.1⟩
        · exact ⟨BitVec.ofNat 64 recordCursor,present.1⟩
    · rw [if_neg zero] at tailRun
      have returnedEq : returned=.val (.word value) := by
        simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst tailRun).symm
      have innerEq : inner=emptyLocalsHOLFinite ready := (congrArg Prod.snd tailRun).symm
      rw [innerEq]
      refine ⟨prefixCursor,current,by omega,prefixFamily.of_control rfl rfl rfl rfl,?_,currentFloors,by intro index; rfl,
        ⟨currentWorld.of_agreement ready _ ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)⟩,
        currentHash.of_fields ready _ stp pad rfl rfl rfl (HeapGlobals.refl ready),currentArena.of_fields ready _ scratchPtr limit rfl rfl,
        HeapGlobals.refl ready,?_,value,returnedEq⟩
      · intro index; have := prefixPopulation index; omega
      · change ready.clock-ready.clock+TableFamily.potential current≤_; omega
  obtain ⟨finalCursor,finalObjects,finalForward,innerFamily,finalPopulation,finalFloors,finalPointers,⟨innerWorld⟩,innerHash,innerArena,tailGlobals,tailPrice,scalar⟩ := tail
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  have endian := congrArg PanSemStateFiniteExact.be frame
  have globalsEq := congrArg PanSemStateFiniteExact.globals frame
  have code := congrArg PanSemStateFiniteExact.code frame
  have oracle := congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.ffi.oracle) frame
  change post.memaddrs=inner.memaddrs at domain
  change post.be=inner.be at endian
  change post.globals=inner.globals at globalsEq
  change post.code=inner.code at code
  change post.ffi.oracle=inner.ffi.oracle at oracle
  have memory := Input.LocalEffects.memory_of_erase inner post frame
  have finalFamily : TableFamily.Model post finalCursor finalObjects := innerFamily.of_control (by rw [globalsEq]) memory domain endian
  let finalWorld := innerWorld.of_agreement inner post ws root nibs cutoff frozenEnd valueLimit domain endian (by rw [globalsEq]) (by rw [globalsEq]) (by intros; rw [memory])
  have finalHash := innerHash.of_fields inner post stp pad domain code oracle (by intro key different; rw [globalsEq])
  have finalArena := innerArena.of_fields inner post scratchPtr limit domain globalsEq
  have finalGlobals : HeapGlobals source post := by intro key different; rw [globalsEq]; exact (tailGlobals key different).trans (prefixGlobals key different)
  have overall := evaluateHOLFiniteState_clock_le source Kind.preState.body
  rw [run] at overall
  change post.clock≤source.clock at overall
  let paid := source.clock-post.clock
  refine ⟨paid,finalCursor,finalObjects,Nat.sub_le _ _,by dsimp [paid]; omega,by omega,finalFamily,finalPopulation,finalFloors,?_,⟨finalWorld⟩,
    finalHash,finalArena,finalGlobals,(Input.evaluation_fields source post Kind.preState.body _ run).2.2.2,?_,scalar⟩
  · intro index; exact (finalPointers index).trans (pointers index)
  · dsimp [paid]; omega

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_body_normal
