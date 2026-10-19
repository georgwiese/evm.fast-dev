import InitECandidate.Solver.GasBudget.PreStateAccountCallNormalValues
import InitECandidate.Solver.Mpt.AccountRegistryValueResult
import InitECandidate.Solver.GasBudget.AccountRequiredFallback

namespace InitECandidate.Solver.GasBudget.AccountRequired
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

set_option maxRecDepth 10000 in
/-- Complete unchanged get_pre_state_account: real optional lookup, actual fallback, and
registered physical result with the shared family potential. -/
theorem pre_state_body_registered {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit count : Nat) (objects : ι → TableFamily.Object) (writer reader recorder : ι)
    (family : TableFamily.Model source cursor objects) (population : ∀ index,(objects index).slots.length≤count)
    (writerKind : (objects writer).kind=.account) (readerKind : (objects reader).kind=.account) (recorderKind : (objects recorder).kind=.account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property)
    (writerOwned : property writer 1#64) (recorderOwned : property recorder 1#64)
    (cacheKnown : ∀ value,property reader value → AccountDecode.Registry.Known accounts value)
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
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source (body .preState)=(some (.returned returned),post)) :
    ∃ paid nextCursor nextObjects nextAccounts word,
      paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤nextCursor ∧ TableFamily.Model post nextCursor nextObjects ∧
      (∀ index,(nextObjects index).slots.length≤count+2) ∧ (∀ index,frozenEnd≤(nextObjects index).floor) ∧
      (∀ index,(nextObjects index).pointer=(objects index).pointer) ∧ Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧
      Keccak256.Environment post stp pad ∧ Rlp.Validation.Arena post scratchPtr limit ∧ HeapGlobals source post ∧ post.code=source.code ∧
      paid+TableFamily.potential objects≤26*count+31101+TableFamily.potential nextObjects ∧
      AccountDecode.Registry post cutoff nextCursor nextObjects nextAccounts ∧ TableFamily.ValuesHave post nextObjects property ∧
      (∀ value : BitVec 64,AccountDecode.Registry.Known accounts value → AccountDecode.Registry.Known nextAccounts value) ∧
      word∈nextAccounts ∧ returned=.val (.word word) ∧ Nonempty (AccountDecode.Image post word) := by
  rw [body_shape .preState] at run
  change evaluateHOLFiniteState source (.decCall (ofString "a") .one (ofString "get_pre_state_account_optional") [localVar "addr"] afterGet)=(some (.returned returned),post) at run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "addr"]=some [.val (.word query)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,queryLocal]
  obtain ⟨prefixPaid,prefixCursor,nextObjects,prefixAccounts,ready,value,inner,funded,prefixClock,forward,nextFamily,nextPopulation,nextFloors,pointers,⟨nextWorld⟩,nextHash,nextArena,prefixGlobals,codeEq,price,nextRegistry,nextValues,weakening,ownership,resultCell,tailRun,restored⟩ :=
    AccountCache.scoped_pre_state_normal_values source post transaction block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit count objects writer reader recorder
      family population writerKind readerKind recorderKind environment installed accounts registry property tableValues writerOwned recorderOwned world afterWorld floors hashEnvironment
      stateArena stateAligned padArena padAligned queryArena stateBelow padBelow arena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena transactionGlobal blockGlobal blockArena blockBefore
      setMapped setCell getMapped getCell recordMapped recordCell "a" [localVar "addr"] afterGet args returned run
  have known := AccountDecode.Registry.known_of_cache accounts prefixAccounts (property reader) weakening cacheKnown value ownership
  obtain ⟨tailPaid,finalCursor,finalAccounts,word,tailPrice,tailFunded,tailClock,more,choice,innerFamily,innerRegistry,innerValues,tailWeakening,member,returnedEq,innerImage,tailGlobals,innerCode,domain,endian,oracle,before⟩ :=
    fallback_normal ready inner value emptyRoot emptyHash cutoff prefixCursor nextObjects writer prefixAccounts nextFamily nextRegistry property nextValues known
      (by have := world.ordered; omega) resultCell
      ((prefixGlobals _ (by decide)).trans rootGlobal) ((prefixGlobals _ (by decide)).trans hashGlobal) nextWorld.domain rootArena hashArena
      (by rw [codeEq]; exact installed) returned tailRun
  let innerWorld := nextWorld.of_agreement ready inner ws root nibs cutoff frozenEnd valueLimit domain endian
    (tailGlobals _ (by decide)) (tailGlobals _ (by decide))
    (fun query needed=>before query (by have := (nextWorld.footprint query needed).2; omega))
  have innerHash := nextHash.of_fields ready inner stp pad domain innerCode oracle tailGlobals
  have innerArena := nextArena.of_heap_globals ready inner scratchPtr limit domain tailGlobals
  have postFamily : TableFamily.Model post finalCursor nextObjects := by rw [restored]; exact innerFamily.of_control rfl rfl rfl rfl
  let postWorld := innerWorld.of_agreement inner post ws root nibs cutoff frozenEnd valueLimit
    (by rw [restored]; rfl) (by rw [restored]; rfl) (by rw [restored]; rfl) (by rw [restored]; rfl) (by intros; rw [restored]; rfl)
  have postHash := innerHash.of_fields inner post stp pad (by rw [restored]; rfl) (by rw [restored]; rfl) (by rw [restored]; rfl) (by rw [restored]; exact HeapGlobals.refl inner)
  have postArena := innerArena.of_fields inner post scratchPtr limit (by rw [restored]; rfl) (by rw [restored]; rfl)
  have postRegistry := innerRegistry.framed inner post cutoff finalCursor finalCursor nextObjects nextObjects finalAccounts
    (TableFamily.PersistentFrame.of_memory cutoff finalCursor nextObjects inner post (by rw [restored] <;> rfl)) (Nat.le_refl _) (by rw [restored] <;> rfl)
  have postValues := innerValues.of_memory inner post nextObjects property (by rw [restored] <;> rfl)
  have globals : HeapGlobals source post := by intro key different; rw [restored]; exact (tailGlobals key different).trans (prefixGlobals key different)
  have postClock : post.clock=inner.clock := by rw [restored]; rfl
  refine ⟨prefixPaid+tailPaid,finalCursor,nextObjects,finalAccounts,word,by omega,by omega,by omega,postFamily,nextPopulation,nextFloors,pointers,⟨postWorld⟩,postHash,postArena,globals,?_,by omega,
    postRegistry,postValues,?_,member,returnedEq,postRegistry.images word member⟩
  · rw [restored]; exact innerCode.trans codeEq
  · intro item old; exact tailWeakening item (weakening item old)

end InitECandidate.Solver.GasBudget.AccountRequired

#print axioms InitECandidate.Solver.GasBudget.AccountRequired.pre_state_body_registered
