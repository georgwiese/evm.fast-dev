import InitECandidate.Solver.Mpt.WsAccountOptionalResult
import InitECandidate.Solver.Mpt.WsAccountOptionalCost
import InitECandidate.Solver.Mpt.WsAccountOptionalGlobals
import InitECandidate.Solver.Mpt.WsAccountOptionalLeafNormal

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Complete original normal witness provider derives its actual optional
account result, retained120-byte reservation or absent heap, restored arena
and source cost. Room for the temporary lookup is derived, not assumed. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit : BitVec 64)
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
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    Result post heap cursor limit returned ∧ heap.toNat+32≤33806089496 ∧ source.clock-post.clock≤191*valueLimit+2593 ∧ HeapGlobals source post := by
  have originalRun := normal
  obtain ⟨allocated,ready,inner,answer,readyCell,result,readyArena,nextHeap,leafGlobals,leafMemory,leafPrice,codeEq,tailRun,restored⟩ :=
    body_leaf source post ws root addr heap nibs stp pad cursor limit cutoff valueLimit data values protectedValues hashData graphProtection valueProtection rootProtection
      addressCell arena heapGlobal heapBound installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code := by rw [codeEq]; exact installed
  have tailResult := after_leaf_normal ready inner heap cursor limit cutoff valueLimit answer readyCell result readyArena nextHeap heapBound heapLower heapAligned
    sizeBound aligned scratchBelow readyInstalled returned tailRun
  have finalResult : Result post heap cursor limit returned := by
    rw [restored]
    exact Result.of_fields inner _ heap cursor limit returned tailResult rfl rfl
  have price := body_cost source ws root addr heap nibs stp pad cursor limit cutoff valueLimit data values protectedValues hashData graphProtection valueProtection rootProtection
    addressCell arena heapGlobal allocated heapLower heapAligned sizeBound aligned scratchBelow installed
  rw [originalRun] at price
  have nonheap : HeapGlobals source post := by
    intro key notHeap
    by_cases scratch : key=ofString "scratch_ptr"
    · subst key
      exact finalResult.1.cursorGlobal.trans arena.cursorGlobal.symm
    · have preserved := globals key source.code installed notHeap scratch source rfl
      rw [originalRun] at preserved
      exact congrArg Prod.snd preserved
  exact ⟨finalResult,allocated,price,nonheap⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_normal
