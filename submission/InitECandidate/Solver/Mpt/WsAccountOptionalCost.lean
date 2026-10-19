import InitECandidate.Solver.Mpt.WsAccountOptionalTailCost
import InitECandidate.Solver.Mpt.WsAccountLeafCursors
import InitECandidate.Solver.Mpt.WsAccountLeafNormal
import InitECandidate.Solver.Mpt.WsAccountLeafCall

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Complete unchanged witness account provider: actual lookup, absence
return or actual account allocation/decoder/return. Payload ownership is a
property of the current physical trie values, retained by the actual lookup.
All entry invariants still require whole-program reachability. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit : BitVec 64)
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
    (room : heap.toNat+32≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤191*valueLimit+2593 := by
  obtain ⟨callee,called,addrCell⟩ := WsAccountLeaf.environment source.code.lookup addr (WsAccountLeaf.original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  let entryData := WsAccountLeaf.Data.of_fields source entry ws root heap nibs data rfl rfl rfl rfl rfl
  let entryValues := TrieWalk.Values.rebase source.memory entry.memory source.memaddrs entry.memaddrs data.graph valueLimit values rfl rfl
  have entryProtected : TrieWalk.ValueProtected entryData.graph nibs := protectedValues
  have entryHash := Keccak256.EntryData.of_fields source entry stp addr pad heap 20 rfl rfl rfl rfl rfl hashData
  have entryGraphProtection : ∀ query,entryData.graph.Footprint query → Keccak256.Protected stp pad heap query := graphProtection
  have entryValueProtection : ∀ query,TrieWalk.ValueFootprint entryData.graph query → Keccak256.Protected stp pad heap query := valueProtection
  have entryArena := Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  have price := WsAccountLeaf.body_cost entry ws root addr heap nibs stp pad entryData entryHash entryGraphProtection rootProtection addrCell heapGlobal room installed
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "addr"]=some (WsAccountLeaf.values addr) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell,WsAccountLeaf.values]
  have joined := Input.ClockCost.scoped_reached_current source "leaf" TrieWalk.resultShape (ofString "ws_account_leaf") [localVar "addr"] _
    WsAccountLeaf.body afterLeaf callee TrieWalk.resultShape 2297 (191*valueLimit+295) args called price (by
      intro target returned normal checked
      obtain ⟨allocated,result⟩ := WsAccountLeaf.body_normal_value entry target ws root addr heap nibs stp pad entryData valueLimit entryValues entryProtected
        entryHash entryGraphProtection entryValueProtection rootProtection addrCell heapGlobal (by omega) installed returned normal
      have nextHeap := WsAccountLeaf.body_heap entry target heap heapGlobal (by omega) installed returned normal
      have nextArena := WsAccountLeaf.body_arena entry target cursor limit entryArena installed _ normal
      have codeEq := (Input.evaluation_fields entry target WsAccountLeaf.body _ normal).2.2.2
      let ready := Input.CallNormal.continuationEntry source target "leaf" returned
      have readyCell : ready.locals.lookup (ofString "leaf")=some returned := Input.CallNormal.continuation_lookup_same _ _ _ _
      have readyArena := Rlp.Validation.Arena.of_fields target ready cursor limit nextArena rfl rfl
      have readyInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
      have tail := after_leaf_cost ready heap cursor limit cutoff valueLimit returned readyCell result readyArena nextHeap (by omega) heapLower heapAligned
        sizeBound aligned scratchBelow readyInstalled
      simpa only [ready,Input.CallNormal.continuationEntry,setVarHOLFinite_clock] using tail)
  rw [body_shape]
  omega

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.body_cost
