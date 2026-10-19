import InitECandidate.Solver.Mpt.WsAccountLeafCost

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (addr : BitVec 64) : List (ValueHOL 64) := [.val (.word addr)]

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (addr : BitVec 64) (known : table (ofString "ws_account_leaf")=some (formals,body,TrieWalk.resultShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "ws_account_leaf") (values addr)=some (body,callee,TrieWalk.resultShape) ∧
      callee.lookup (ofString "addr")=some (.val (.word addr)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values addr).length ∧
      ((formals.zip (values addr)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact table (ofString "ws_account_leaf") (values addr)=some (body,Input.CallNormal.unaryLocals "addr" addr,TrieWalk.resultShape) := by
    simp only [lookupCodeHOLExact,known,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [Input.CallNormal.unaryLocals]

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (room : h.toNat+32≤33806089496)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values addr))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "ws_account_leaf") arguments)).2.clock≤2298 := by
  obtain ⟨callee,called,addressLocal⟩ := environment source.code.lookup addr (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  let entryData := Data.of_fields source entry ws root h nibs data rfl rfl rfl rfl rfl
  have entryHashData := Keccak256.EntryData.of_fields source entry stp addr pad h 20 rfl rfl rfl rfl rfl hashData
  have entryProtection : ∀ query,entryData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have cost := body_cost entry ws root addr h nibs stp pad entryData entryHashData entryProtection rootProtection addressLocal heap room installed
  exact Input.ClockCost.call_current source destination (ofString "ws_account_leaf") arguments _ body callee TrieWalk.resultShape 2297 args called cost

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.environment
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.call_cost
