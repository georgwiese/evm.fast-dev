import InitECandidate.Solver.Mpt.WsAccountOptionalTailFixedPrice
import InitECandidate.Solver.Mpt.WsAccountOptionalLeafNormal

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real absent/present selection retains the successful decoder's
fixed source price, without paying the maximum witness size per query. -/
theorem after_leaf_fixed_price (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit emptyRoot emptyHash : BitVec 64) (cutoff valueLimit : Nat)
    (answer : ValueHOL 64) (leafCell : source.locals.lookup (ofString "leaf")=some answer)
    (result : TrieWalk.Answer source.memaddrs valueLimit answer (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) : source.clock-post.clock≤28753 := by
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
    simp [emptyLocalsHOLFinite]
  · rw [found] at leafCell
    have actual : evaluateHOLFiniteState source afterLeaf=evaluateHOLFiniteState source afterGuard := by
      rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
      simp [field,evalHOLExact,localVar,toExact,leafCell,TrieWalk.triple,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    have passed := actual.symm.trans normal
    exact after_guard_fixed_price source post pointer length heap cursor limit emptyRoot emptyHash cutoff leafCell arena heapGlobal heapBound heapLower heapAligned
      before (by have := payload.1; omega) aligned scratchBelow inputAbove rootGlobal hashGlobal installed returned passed

/-- Every actual normal original provider costs at most31051 source ticks,
independent of the maximum encoded witness leaf length. The bounds on the
real returned account leaf and every paid prefix are derived from execution. -/
theorem body_fixed_price (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit emptyRoot emptyHash : BitVec 64)
    (cutoff valueLimit : Nat) (data : WsAccountLeaf.Data source ws root heap nibs)
    (values : TrieWalk.Values data.graph valueLimit (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad heap 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad heap query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad heap query)
    (rootProtection : Keccak256.Protected stp pad heap (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : source.clock-post.clock≤31051 := by
  obtain ⟨allocated,ready,inner,answer,readyCell,result,readyArena,nextHeap,leafGlobals,leafMemory,leafPrice,codeEq,tailRun,restored⟩ :=
    body_leaf source post ws root addr heap nibs stp pad cursor limit cutoff valueLimit data values protectedValues hashData graphProtection valueProtection rootProtection
      addressCell arena heapGlobal heapBound installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [codeEq]; exact installed
  have tailPrice := after_leaf_fixed_price ready inner heap cursor limit emptyRoot emptyHash cutoff valueLimit answer readyCell result readyArena nextHeap heapBound heapLower heapAligned
    sizeBound aligned scratchBelow ((leafGlobals _ (by decide)).trans rootGlobal) ((leafGlobals _ (by decide)).trans hashGlobal) readyInstalled returned tailRun
  rw [restored]
  change source.clock-inner.clock≤31051
  omega

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_leaf_fixed_price
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_fixed_price
