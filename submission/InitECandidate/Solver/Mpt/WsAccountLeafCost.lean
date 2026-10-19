import InitECandidate.Solver.Mpt.WsAccountLeafAllocCost

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete unchanged ws_account_leaf. The actual mark, temporary32-byte
allocation, address hash, trie lookup and release are priced from current
physical entry facts. This is a source-clock bound, not a target-work bound. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (room : h.toNat+32≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2297 := by
  by_cases zero : source.clock=0
  · omega
  have positive : 1≤source.clock := by omega
  let ready := bind {source with clock := source.clock-1} "mark" h
  let readyData := Data.of_fields source ready ws root h nibs data rfl rfl rfl rfl rfl
  have readyHashData := Keccak256.EntryData.of_fields source ready stp addr pad h 20 rfl rfl rfl rfl rfl hashData
  have readyGraphProtection : ∀ query,readyData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word addr)) :=
    (bind_lookup_other _ "mark" "addr" h (by decide)).trans addressCell
  have priced := after_mark_cost ready ws root addr h nibs stp pad readyData readyHashData readyGraphProtection rootProtection readyAddress heap room installed
  have monotone := evaluateHOLFiniteState_clock_le ready afterMark
  have actual := Input.HeapScope.mark_call_execute source h "mark" afterMark heap (Input.HeapScope.mark_original_code source.code installed) positive
  rw [body_shape,actual]
  change source.clock-(evaluateHOLFiniteState ready afterMark).2.clock≤2297
  change source.clock-1-(evaluateHOLFiniteState ready afterMark).2.clock≤2296 at priced
  change (evaluateHOLFiniteState ready afterMark).2.clock≤source.clock-1 at monotone
  omega

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_cost
