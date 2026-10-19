import InitECandidate.Solver.Mpt.WsAccountOptionalTailImage
import InitECandidate.Solver.Mpt.WsAccountOptionalResult

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Actual absent/present selection derives the physical image when present
and preserves earlier persistent words on both branches. -/
theorem after_leaf_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit emptyRoot emptyHash : BitVec 64) (cutoff valueLimit : Nat)
    (answer : ValueHOL 64) (leafCell : source.locals.lookup (ofString "leaf")=some answer)
    (result : TrieWalk.Answer source.memaddrs valueLimit answer (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) :
    (returned=.val (.word 1#64) ∨ Nonempty (AccountDecode.Image post heap)) ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat → post.memory query=source.memory query) := by
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
    exact ⟨Or.inl returnedEq,by intros; rfl⟩
  · rw [found] at leafCell
    have actual : evaluateHOLFiniteState source afterLeaf=evaluateHOLFiniteState source afterGuard := by
      rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
      simp [field,evalHOLExact,localVar,toExact,leafCell,TrieWalk.triple,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have passed := actual.symm.trans normal
    obtain ⟨image,window⟩ := after_guard_image source post pointer length heap cursor limit emptyRoot emptyHash cutoff leafCell arena heapGlobal heapBound heapLower heapAligned
      before (by have := payload.1; omega) aligned scratchBelow inputAbove rootGlobal hashGlobal rootArena hashArena installed returned passed
    exact ⟨Or.inr image,window⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_leaf_image
