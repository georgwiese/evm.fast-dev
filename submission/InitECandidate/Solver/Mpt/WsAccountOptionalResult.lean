import InitECandidate.Solver.Mpt.WsAccountOptionalTailNormal

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual optional account results: absent uses the original sentinel1 and
no persistent reservation; present returns the old heap with120 bytes kept. -/
def Result (post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) (value : ValueHOL 64) : Prop :=
  Rlp.Validation.Arena post cursor limit ∧
    ((value=.val (.word 1#64) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) ∨
      (value=.val (.word heap) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word (heap+120#64))) ∧ heap.toNat+120≤33806089496))

theorem Result.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) (value : ValueHOL 64)
    (result : Result source heap cursor limit value) (domain : target.memaddrs=source.memaddrs) (globals : target.globals=source.globals) :
    Result target heap cursor limit value := by
  refine ⟨Rlp.Validation.Arena.of_fields source target cursor limit result.1 domain globals,?_⟩
  simpa only [globals] using result.2

set_option maxRecDepth 10000 in
/-- A normal reached provider suffix chooses the actual absent or allocated
result from the real lookup answer. No future allocation/decode is supplied. -/
theorem after_leaf_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) (cutoff valueLimit : Nat)
    (answer : ValueHOL 64) (leafCell : source.locals.lookup (ofString "leaf")=some answer)
    (result : TrieWalk.Answer source.memaddrs valueLimit answer (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) : Result post heap cursor limit returned := by
  rcases result with absent | ⟨pointer,length,found,payload,inputAbove,before⟩
  · rw [absent] at leafCell
    have actual : evaluateHOLFiniteState source afterLeaf=(some (.returned (.val (.word 1#64))),emptyLocalsHOLFinite source) := by
      rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
      simp [field,evalHOLExact,localVar,toExact,leafCell,TrieWalk.triple,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        evaluateHOLFiniteState_return,shapeOfHOLExact,emptyLocalsHOLFinite]
    have joined := actual.symm.trans normal
    have returnedEq : returned=.val (.word 1#64) := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst joined).symm
    have postEq : post=emptyLocalsHOLFinite source := (congrArg Prod.snd joined).symm
    rw [postEq]
    exact ⟨Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl,Or.inl ⟨returnedEq,heapGlobal⟩⟩
  · rw [found] at leafCell
    have actual : evaluateHOLFiniteState source afterLeaf=evaluateHOLFiniteState source afterGuard := by
      rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
      simp [field,evalHOLExact,localVar,toExact,leafCell,TrieWalk.triple,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have passed := actual.symm.trans normal
    obtain ⟨returnedEq,nextArena,nextHeap,room⟩ := after_guard_normal source post pointer length heap cursor limit cutoff leafCell arena heapGlobal heapBound heapLower heapAligned
      before (by have := payload.1; omega) aligned scratchBelow inputAbove installed returned passed
    exact ⟨nextArena,Or.inr ⟨returnedEq,nextHeap,room⟩⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.Result.of_fields
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_leaf_normal
