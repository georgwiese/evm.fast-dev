import InitECandidate.Solver.GasBudget.PreStateAccountMissCompleteValues
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
  obtain ⟨paid,recordCursor,next,nextCursor,nextAccounts,funded,clock,forward,nextKind,choice,nextFamily,pointers,floors,price,countLower,countUpper,capacity,nextWorld,nextHash,result,globals,codes,image,_,_,_,_⟩ :=
    pre_state_miss_complete_values source post block query ws root nibs stp pad scratchPtr limit emptyRoot emptyHash cursor cutoff frozenEnd valueLimit objects writer
      family kind tableEnvironment installed [] (AccountDecode.Registry.empty source cutoff cursor objects)
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro world afterWorld floors hashEnvironment stateArena stateAligned padArena padAligned queryArena stateBelow padBelow
      arena scratchBelow aligned sizeBound rootGlobal hashGlobal rootArena hashArena blockGlobal mapped stored queryLocal returned run
  exact ⟨paid,recordCursor,next,nextCursor,funded,clock,forward,nextKind,choice,nextFamily,pointers,floors,price,countLower,countUpper,capacity,nextWorld,nextHash,result,globals,codes,image⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_complete
