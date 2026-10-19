import InitECandidate.Solver.Mpt.WsAccountOptionalProgram
import InitECandidate.Solver.Mpt.WsAccountLeafNormal
import InitECandidate.Solver.Mpt.WsAccountLeafCall
import InitECandidate.Solver.Mpt.WsAccountLeafMemory
import InitECandidate.Solver.Mpt.WsAccountLeafCursors
import InitECandidate.Solver.Mpt.LookupGlobals
import InitECandidate.Solver.Input.CallNormal
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Invert the complete original provider's actual first call once, exposing
its reached leaf answer, arena, saved heap and global frame for every real
normal continuation. No future lookup or allocation result is supplied. -/
theorem body_leaf (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit : BitVec 64)
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
    (heapBound : heap.toNat≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    heap.toNat+32≤33806089496 ∧ ∃ ready inner answer,
      ready.locals.lookup (ofString "leaf")=some answer ∧
      TrieWalk.Answer ready.memaddrs valueLimit answer (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat) ∧
      Rlp.Validation.Arena ready cursor limit ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      HeapGlobals source ready ∧ WsAccountLeaf.MemoryFrame source ready stp pad heap nibs ∧ ready.code=source.code ∧
      evaluateHOLFiniteState ready afterLeaf=(some (.returned returned),inner) ∧ post=restore source "leaf" inner := by
  rw [body_shape] at normal
  obtain ⟨callee,called,addrCell⟩ := WsAccountLeaf.environment source.code.lookup addr (WsAccountLeaf.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "addr"]=some (WsAccountLeaf.values addr) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell,WsAccountLeaf.values]
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post "leaf" TrieWalk.resultShape
    (ofString "ws_account_leaf") [localVar "addr"] _ WsAccountLeaf.body afterLeaf callee TrieWalk.resultShape args called returned normal
  let entry := callEntryStateHOLFinite source callee
  let entryData := WsAccountLeaf.Data.of_fields source entry ws root heap nibs data rfl rfl rfl rfl rfl
  let entryValues := TrieWalk.Values.rebase source.memory entry.memory source.memaddrs entry.memaddrs data.graph valueLimit values rfl rfl
  have entryProtected : TrieWalk.ValueProtected entryData.graph nibs := protectedValues
  have entryHash := Keccak256.EntryData.of_fields source entry stp addr pad heap 20 rfl rfl rfl rfl rfl hashData
  have entryGraphProtection : ∀ query,entryData.graph.Footprint query → Keccak256.Protected stp pad heap query := graphProtection
  have entryValueProtection : ∀ query,TrieWalk.ValueFootprint entryData.graph query → Keccak256.Protected stp pad heap query := valueProtection
  have entryArena := Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  obtain ⟨allocated,result⟩ := WsAccountLeaf.body_normal_value entry target ws root addr heap nibs stp pad entryData valueLimit entryValues entryProtected
    entryHash entryGraphProtection entryValueProtection rootProtection addrCell heapGlobal heapBound installed answer bodyRun
  have nextHeap := WsAccountLeaf.body_heap entry target heap heapGlobal heapBound installed answer bodyRun
  have nextArena := WsAccountLeaf.body_arena entry target cursor limit entryArena installed _ bodyRun
  have codeEq := (Input.evaluation_fields entry target WsAccountLeaf.body _ bodyRun).2.2.2
  let ready := Input.CallNormal.continuationEntry source target "leaf" answer
  have readyCell : ready.locals.lookup (ofString "leaf")=some answer := Input.CallNormal.continuation_lookup_same _ _ _ _
  have readyArena := Rlp.Validation.Arena.of_fields target ready cursor limit nextArena rfl rfl
  have nonheap : HeapGlobals source ready := by
    intro key notHeap
    have preserved := WsAccountLeaf.globals key source.code installed notHeap entry rfl
    rw [bodyRun] at preserved
    exact congrArg Prod.snd preserved
  have memory := WsAccountLeaf.body_memory entry target ws root addr heap nibs stp pad entryData entryHash entryGraphProtection rootProtection
    addrCell heapGlobal heapBound installed answer bodyRun
  exact ⟨allocated,ready,inner,answer,readyCell,result,readyArena,nextHeap,nonheap,memory,codeEq,tailRun,restored⟩

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_leaf
