import InitECandidate.Solver.GasBudget.PreStateAccountMiss
import InitECandidate.Solver.Mpt.WsAccountOptionalWorldCall
import InitECandidate.Solver.Rlp.ValidationHeapGlobals

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout Mpt

/-- Complete actual normal block-cache miss: real read recording, possible
table growth, original witness provider and return. Current witness/table
ownership is retained through both actual phases, and the combined source
price uses the fixed successful provider bound rather than witness size. -/
theorem pre_state_miss_complete {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash : BitVec 64)
    (cursor cutoff frozenEnd valueLimit : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind=.account)
    (tableEnvironment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (world : WsAccountLeaf.World source ws root nibs cutoff frozenEnd valueLimit) (afterWorld : frozenEnd≤cursor) (floors : ∀ index,frozenEnd≤(objects index).floor)
    (hashEnvironment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0) (queryArena : AllocatedBytes.Arena query 20)
    (stateBelow : stp.toNat+200≤cutoff) (padBelow : pad.toNat+136≤cutoff)
    (arena : Rlp.Validation.Arena source scratchPtr limit) (scratchBelow : scratchPtr.toNat≤cutoff) (aligned : cutoff%8=0) (sizeBound : 16*valueLimit<2^64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (blockGlobal : source.globals.lookup (ofString "bs")=some (.val (.word block)))
    (mapped : source.memaddrs (block+72#64)) (stored : source.memory (block+72#64)=.word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr")=some (.val (.word query)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source Kind.preState.afterMiss=(some (.returned returned),post)) :
    ∃ paid recordCursor next nextCursor,
      paid≤source.clock ∧ post.clock=source.clock-paid ∧ cursor≤recordCursor ∧ next.kind=.account ∧
      (nextCursor=recordCursor ∨ nextCursor=recordCursor+120) ∧ TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      (∀ index,(Function.update objects writer next index).pointer=(objects index).pointer) ∧
      (∀ index,(Function.update objects writer next index).floor=(objects index).floor) ∧
      paid+GrowRuntime.growthPotential .account (objects writer).plan.capacity≤9*(objects writer).slots.length+31065+GrowRuntime.growthPotential .account next.plan.capacity ∧
      (objects writer).slots.length≤next.slots.length ∧ next.slots.length≤(objects writer).slots.length+1 ∧
      next.plan.capacity≤max (objects writer).plan.capacity (4*(next.slots.length+1)) ∧
      Nonempty (WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit) ∧ Keccak256.Environment post stp pad ∧
      WsAccountOptional.Result post (BitVec.ofNat 64 recordCursor) scratchPtr limit returned ∧ HeapGlobals source post ∧ post.code=source.code ∧
      (returned=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image post (BitVec.ofNat 64 recordCursor))) := by
  obtain ⟨recordPaid,recordCursor,next,recordReady,funded,recordClock,forward,nextKind,amortized,recordFamily,pointers,countLower,countUpper,capacity,codeEq,oracleEq,nextTableEnvironment,recordGlobals,floorFrame,queryCell,providerRun⟩ :=
    pre_state_miss_normal source post block query cursor objects writer family kind tableEnvironment installed blockGlobal mapped stored queryLocal
      (by have := queryArena.upper; omega)
      (fun offset active=>AllocatedBytes.byte_mapped source query 20 offset world.domain queryArena active) returned run
  have domain : recordReady.memaddrs=source.memaddrs := nextTableEnvironment.domain.trans tableEnvironment.domain.symm
  have endian : recordReady.be=source.be := nextTableEnvironment.little.trans tableEnvironment.little.symm
  let currentWorld := world.after_family source recordReady ws root nibs cutoff frozenEnd valueLimit objects (Function.update objects writer next) floorFrame floors domain endian recordGlobals
  have currentEnvironment := hashEnvironment.of_fields source recordReady stp pad domain codeEq oracleEq recordGlobals
  have currentArena := arena.of_heap_globals source recordReady scratchPtr limit domain recordGlobals
  have currentTable := recordFamily.tables writer
  let heap := BitVec.ofNat 64 recordCursor
  have heapNumber : heap.toNat=recordCursor := by
    change (BitVec.ofNat 64 recordCursor).toNat=recordCursor
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := currentTable.bounded; omega)]
  have currentFamily : TableFamily.Model recordReady heap.toNat (Function.update objects writer next) := by rw [heapNumber]; exact recordFamily
  have currentFloors : ∀ index,frozenEnd≤(Function.update objects writer next index).floor := by
    intro index
    rw [floorFrame.floors index]
    exact floors index
  have currentInstalled : Input.OriginalCode.Installed recordReady.code := by rw [codeEq]; exact installed
  have args : evalListHOLFinite recordReady (h:=fun address=>Classical.propDecidable (recordReady.memaddrs address)) [localVar "addr"]=some [.val (.word query)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,queryCell]
  obtain ⟨positive,ready,answer,inner,nextCursor,answerCell,choice,nextFamily,⟨nextWorld⟩,nextHashEnvironment,result,providerGlobals,providerFrame,providerMemory,providerCode,price,image,returnRun,restored⟩ :=
    WsAccountOptional.scoped_world_family recordReady post ws root query heap nibs stp pad scratchPtr limit emptyRoot emptyHash cutoff frozenEnd valueLimit currentWorld currentEnvironment
      stateArena stateAligned padArena padAligned queryArena stateBelow padBelow (Function.update objects writer next) currentFamily currentFloors currentArena currentTable.heap
      (by rw [heapNumber]; exact currentTable.bounded) (by rw [heapNumber]; exact currentTable.aligned) (by rw [heapNumber]; omega)
      sizeBound aligned scratchBelow ((recordGlobals _ (by decide)).trans rootGlobal) ((recordGlobals _ (by decide)).trans hashGlobal) rootArena hashArena currentInstalled
      "a" [localVar "addr"] (.return (localVar "a")) args returned providerRun
  have actual := Input.return_normal ready inner (localVar "a") returned returnRun
  have read : eval ready (localVar "a")=some answer := by simp [eval,evalHOLExact,localVar,toExact,answerCell]
  have returnedEq : returned=answer := Option.some.inj (actual.1.symm.trans read)
  have postEq : post=restore recordReady "a" (emptyLocalsHOLFinite ready) := by rw [restored,actual.2]
  have finalFamily : TableFamily.Model post nextCursor (Function.update objects writer next) := by
    rw [postEq]
    exact nextFamily.of_control rfl rfl rfl rfl
  have finalWorld : WsAccountLeaf.World post ws root nibs cutoff frozenEnd valueLimit := nextWorld.of_agreement ready post ws root nibs cutoff frozenEnd valueLimit
    (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by intro query needed; rw [postEq]; rfl)
  have finalGlobals : HeapGlobals source post := by
    rw [postEq]
    exact recordGlobals.trans providerGlobals
  have finalHashEnvironment := nextHashEnvironment.of_fields ready post stp pad (by rw [postEq]; rfl) (by rw [postEq]; rfl)
    (by rw [postEq]; rfl) (by rw [postEq]; exact HeapGlobals.refl ready)
  have finalResult : WsAccountOptional.Result post heap scratchPtr limit returned := by
    rw [returnedEq,postEq]
    exact WsAccountOptional.Result.of_fields ready _ heap scratchPtr limit answer result rfl rfl
  have finalImage : returned=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image post heap) := by
    rw [returnedEq]
    rcases image with absent | image
    · exact Or.inl absent
    · obtain ⟨current⟩ := image
      exact Or.inr ⟨AccountDecode.Image.of_agreement ready post heap current (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl)⟩
  have postClock : post.clock=ready.clock := by rw [postEq]; rfl
  have overall := evaluateHOLFiniteState_clock_le source Kind.preState.afterMiss
  rw [run] at overall
  change post.clock≤source.clock at overall
  let paid := source.clock-post.clock
  refine ⟨paid,recordCursor,next,nextCursor,Nat.sub_le _ _,by dsimp [paid]; omega,forward,nextKind,?_,finalFamily,pointers,floorFrame.floors,?_,countLower,countUpper,capacity,
    ⟨finalWorld⟩,finalHashEnvironment,finalResult,finalGlobals,?_,finalImage⟩
  · simpa only [heapNumber] using choice
  · dsimp [paid]
    omega
  · rw [postEq]
    exact providerCode.trans codeEq

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_complete
