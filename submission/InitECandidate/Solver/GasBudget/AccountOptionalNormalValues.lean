import InitECandidate.Solver.GasBudget.AccountCacheWorldPrefixValues
import InitECandidate.Solver.GasBudget.AccountCacheDispatch
import InitECandidate.Solver.GasBudget.PreStateAccountCallNormalValues

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

set_option maxRecDepth 10000 in
/-- Complete original get_account_optional normal execution, through both
transaction and block caches and their actual provider misses. Runtime and
current ownership are retained with one shared family potential; cache-hit
value ownership remains a separate invariant. -/
theorem transaction_body_normal_values {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (queryLocal : source.locals.lookup (ofString "addr")=some (.val (.word query)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source Kind.transaction.body=(some (.returned returned),post)) :
    ∃ paid nextCursor nextObjects nextAccounts,paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤nextCursor ∧ TableFamily.Model post nextCursor nextObjects ∧
      (∀ index,(nextObjects index).slots.length≤count+3) ∧ (∀ index,frozenEnd≤(nextObjects index).floor) ∧
      (∀ index,(nextObjects index).pointer=(objects index).pointer) ∧ Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment post stp pad ∧ Rlp.Validation.Arena post scratchPtr limit ∧ HeapGlobals source post ∧ post.code=source.code ∧
      paid+TableFamily.potential objects≤43*count+31147+TableFamily.potential nextObjects ∧
      AccountDecode.Registry post cutoff nextCursor nextObjects nextAccounts ∧ TableFamily.ValuesHave post nextObjects property ∧
      AccountDecode.Registry.Extension accounts nextAccounts cursor ∧
      ∃ value : BitVec 64,returned=.val (.word value) ∧ (property reader value ∨ property blockReader value ∨ AccountDecode.Registry.Known nextAccounts value) := by
  obtain ⟨prefixPaid,prefixCursor,next,flag,value,ready,inner,funded,prefixClock,forward,nextKind,countLower,countUpper,capacity,prefixFamily,prefixPopulation,pointers,prefixPrice,⟨currentWorld⟩,currentHash,currentArena,currentEnvironment,codeEq,prefixGlobals,floorFrame,beforeWords,queryCell,resultCell,tailRun,frame,postClock,prefixValues,valueOwnership,persistent⟩ :=
    world_cache_prefix_values .transaction source post transaction transaction query ws root nibs stp pad scratchPtr limit cursor cutoff frozenEnd valueLimit count objects writer reader
      family population writerKind readerKind environment installed property tableValues writerOwned world floors hashEnvironment arena queryArena transactionGlobal transactionGlobal
      (by omega) setMapped setCell getMapped getCell queryLocal returned run
  let current := Function.update objects writer next
  change ∀ index,(current index).slots.length≤count+1 at prefixPopulation
  change prefixPaid+TableFamily.potential objects≤17*count+23+TableFamily.potential current at prefixPrice
  have currentFloors : ∀ index,frozenEnd≤(current index).floor := by intro index; rw [floorFrame.floors index]; exact floors index
  have currentKind (index : ι) (oldKind : (objects index).kind=.account) : (current index).kind=.account := by
    by_cases same : index=writer
    · subst index; simpa only [current,Function.update_self] using nextKind
    · simpa only [current,Function.update_of_ne same] using oldKind
  have prefixDomain : ready.memaddrs=source.memaddrs := currentEnvironment.domain.trans environment.domain.symm
  have registryFrame : TableFamily.PersistentFrame cutoff cursor objects current source ready :=
    ⟨fun address lower earlier outside=>persistent.words address (Nat.zero_le _) earlier outside⟩
  have currentRegistry := registry.framed source ready cutoff cursor prefixCursor objects current accounts registryFrame forward prefixDomain
  have tail : ∃ finalCursor finalObjects finalAccounts,prefixCursor≤finalCursor ∧ TableFamily.Model inner finalCursor finalObjects ∧
      (∀ index,(finalObjects index).slots.length≤count+3) ∧ (∀ index,frozenEnd≤(finalObjects index).floor) ∧
      (∀ index,(finalObjects index).pointer=(current index).pointer) ∧ Nonempty (WsAccountLeaf.World inner ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment inner stp pad ∧ Rlp.Validation.Arena inner scratchPtr limit ∧ HeapGlobals ready inner ∧
      ready.clock-inner.clock+TableFamily.potential current≤26*count+31124+TableFamily.potential finalObjects ∧
      AccountDecode.Registry inner cutoff finalCursor finalObjects finalAccounts ∧ TableFamily.ValuesHave inner finalObjects property ∧
      AccountDecode.Registry.Extension accounts finalAccounts prefixCursor ∧
      ∃ word : BitVec 64,returned=.val (.word word) ∧ (property reader word ∨ property blockReader word ∨ AccountDecode.Registry.Known finalAccounts word) := by
    rw [cache_dispatch .transaction ready flag value resultCell] at tailRun
    by_cases zero : flag=0#64
    · rw [if_pos zero] at tailRun
      change evaluateHOLFiniteState ready AccountOptional.afterMiss=(some (.returned returned),inner) at tailRun
      rw [AccountOptional.miss_shape] at tailRun
      have domain : ready.memaddrs=source.memaddrs := currentEnvironment.domain.trans environment.domain.symm
      have keptTransaction (offset : Nat) (inside : offset<72) : ready.memory (transaction+BitVec.ofNat 64 offset)=source.memory (transaction+BitVec.ofNat 64 offset) := by
        have number := byteAddress_toNat transaction offset (by have := transactionArena.upper; omega)
        apply beforeWords
        change (byteAddress transaction offset).toNat<(objects writer).floor
        rw [number]
        omega
      have keptBlock (offset : Nat) (inside : offset<80) : ready.memory (block+BitVec.ofNat 64 offset)=source.memory (block+BitVec.ofNat 64 offset) := by
        have number := byteAddress_toNat block offset (by have := blockArena.upper; omega)
        apply beforeWords
        change (byteAddress block offset).toNat<(objects writer).floor
        rw [number]
        omega
      have setPointer : (current writer).pointer=(objects writer).pointer := pointers writer
      have getPointer : (current blockReader).pointer=(objects blockReader).pointer := pointers blockReader
      have recordPointer : (current recorder).pointer=(objects recorder).pointer := pointers recorder
      have currentSet : ready.memory (transaction+8#64)=.word (current writer).pointer := by rw [keptTransaction 8 (by decide),setCell,setPointer]
      have currentGet : ready.memory (block+16#64)=.word (current blockReader).pointer := by rw [keptBlock 16 (by decide),blockGetCell,getPointer]
      have currentRecord : ready.memory (block+72#64)=.word (current recorder).pointer := by rw [keptBlock 72 (by decide),recordCell,recordPointer]
      have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address)) [localVar "addr"]=some [.val (.word query)] := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,queryCell]
      obtain ⟨paid,finalCursor,finalObjects,finalAccounts,answerReady,word,returnedInner,paidFits,answerClock,more,finalFamily,finalPopulation,finalFloors,stable,⟨finalWorld⟩,finalHash,finalArena,calleeGlobals,calleeCode,price,answerRegistry,answerValues,weakening,answerOwnership,answerCell,returnRun,restored⟩ :=
        scoped_pre_state_normal_values ready inner transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash prefixCursor cutoff frozenEnd valueLimit (count+1)
          current writer blockReader recorder prefixFamily prefixPopulation (currentKind writer writerKind) (currentKind blockReader blockReaderKind) (currentKind recorder recorderKind)
          currentEnvironment (by rw [codeEq]; exact installed) accounts currentRegistry property prefixValues writerOwned recorderOwned currentWorld (by omega) currentFloors currentHash
          stateArena stateAligned padArena padAligned queryArena stateBelow padBelow currentArena scratchBelow aligned sizeBound
          ((prefixGlobals _ (by decide)).trans rootGlobal) ((prefixGlobals _ (by decide)).trans hashGlobal) rootArena hashArena
          ((prefixGlobals _ (by decide)).trans transactionGlobal) ((prefixGlobals _ (by decide)).trans blockGlobal) blockArena
          (by rw [floorFrame.floors writer]; exact blockBefore) (by rw [domain]; exact setMapped) currentSet (by rw [domain]; exact blockGetMapped) currentGet
          (by rw [domain]; exact recordMapped) currentRecord "a" [localVar "addr"] (.return (localVar "a")) args returned tailRun
      have actual := Input.return_normal answerReady returnedInner (localVar "a") returned returnRun
      have read : eval answerReady (localVar "a")=some (.val (.word word)) := by simp [eval,evalHOLExact,localVar,toExact,answerCell]
      have returnedEq : returned=.val (.word word) := Option.some.inj (actual.1.symm.trans read)
      have innerEq : inner=restore ready "a" (emptyLocalsHOLFinite answerReady) := by rw [restored,actual.2]
      have models : TableFamily.Model inner finalCursor finalObjects := by rw [innerEq]; exact finalFamily.of_control rfl rfl rfl rfl
      let innerWorld := finalWorld.of_agreement answerReady inner ws root nibs cutoff frozenEnd valueLimit
        (by rw [innerEq]; rfl) (by rw [innerEq]; rfl) (by rw [innerEq]; rfl) (by rw [innerEq]; rfl) (by intros; rw [innerEq]; rfl)
      have innerHash := finalHash.of_fields answerReady inner stp pad (by rw [innerEq]; rfl) (by rw [innerEq]; rfl) (by rw [innerEq]; rfl) (by rw [innerEq]; exact HeapGlobals.refl answerReady)
      have innerArena := finalArena.of_fields answerReady inner scratchPtr limit (by rw [innerEq]; rfl) (by rw [innerEq]; rfl)
      have globals : HeapGlobals ready inner := by rw [innerEq]; exact calleeGlobals
      have innerRegistry := answerRegistry.framed answerReady inner cutoff finalCursor finalCursor finalObjects finalObjects finalAccounts
        (TableFamily.PersistentFrame.of_memory cutoff finalCursor finalObjects answerReady inner (by rw [innerEq] <;> rfl)) (Nat.le_refl _) (by rw [innerEq] <;> rfl)
      have innerValues := answerValues.of_memory answerReady inner finalObjects property (by rw [innerEq] <;> rfl)
      have paidEq : ready.clock-inner.clock=paid := by rw [innerEq]; change ready.clock-answerReady.clock=paid; omega
      exact ⟨finalCursor,finalObjects,finalAccounts,more,models,finalPopulation,finalFloors,stable,⟨innerWorld⟩,innerHash,innerArena,globals,
        (by rw [paidEq]; omega),innerRegistry,innerValues,weakening,word,returnedEq,Or.inr answerOwnership⟩
    · rw [if_neg zero] at tailRun
      have returnedEq : returned=.val (.word value) := by
        simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst tailRun).symm
      have innerEq : inner=emptyLocalsHOLFinite ready := (congrArg Prod.snd tailRun).symm
      have owned : property reader value := by
        rcases valueOwnership with absent | owned
        · exact (zero absent).elim
        · exact owned
      rw [innerEq]
      have innerRegistry := currentRegistry.framed ready (emptyLocalsHOLFinite ready) cutoff prefixCursor prefixCursor current current accounts
        (TableFamily.PersistentFrame.of_memory cutoff prefixCursor current ready (emptyLocalsHOLFinite ready) rfl) (Nat.le_refl _) rfl
      refine ⟨prefixCursor,current,accounts,by omega,prefixFamily.of_control rfl rfl rfl rfl,?_,currentFloors,by intro index; rfl,
        ⟨currentWorld.of_agreement ready _ ws root nibs cutoff frozenEnd valueLimit rfl rfl rfl rfl (by intros; rfl)⟩,
        currentHash.of_fields ready _ stp pad rfl rfl rfl (HeapGlobals.refl ready),currentArena.of_fields ready _ scratchPtr limit rfl rfl,
        HeapGlobals.refl ready,?_,innerRegistry,prefixValues,AccountDecode.Registry.Extension.refl accounts prefixCursor,value,returnedEq,Or.inl owned⟩
      · intro index; have := prefixPopulation index; omega
      · change ready.clock-ready.clock+TableFamily.potential current≤_; omega
  obtain ⟨finalCursor,finalObjects,finalAccounts,finalForward,innerFamily,finalPopulation,finalFloors,finalPointers,⟨innerWorld⟩,innerHash,innerArena,tailGlobals,tailPrice,innerRegistry,innerValues,weakening,scalar⟩ := tail
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
  have finalRegistry := innerRegistry.framed inner post cutoff finalCursor finalCursor finalObjects finalObjects finalAccounts
    (TableFamily.PersistentFrame.of_memory cutoff finalCursor finalObjects inner post memory) (Nat.le_refl _) domain
  have finalValues := innerValues.of_memory inner post finalObjects property memory.symm
  have overall := evaluateHOLFiniteState_clock_le source Kind.transaction.body
  rw [run] at overall
  change post.clock≤source.clock at overall
  let paid := source.clock-post.clock
  refine ⟨paid,finalCursor,finalObjects,finalAccounts,Nat.sub_le _ _,by dsimp [paid]; omega,by omega,finalFamily,finalPopulation,finalFloors,?_,⟨finalWorld⟩,
    finalHash,finalArena,finalGlobals,(Input.evaluation_fields source post Kind.transaction.body _ run).2.2.2,?_,finalRegistry,finalValues,weakening.lower forward,scalar⟩
  · intro index; exact (finalPointers index).trans (pointers index)
  · dsimp [paid]; omega

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.transaction_body_normal_values
