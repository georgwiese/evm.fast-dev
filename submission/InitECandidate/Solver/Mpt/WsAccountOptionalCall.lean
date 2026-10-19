import InitECandidate.Solver.Mpt.WsAccountOptionalCost

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Genuine scoped caller of the unchanged provider. A pure final return
has tailPrice0; other callers can supply a separately proved continuation
bound. Current data are transported to the actual callee entry. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr heap nibs stp pad cursor limit : BitVec 64)
    (cutoff valueLimit : Nat) (data : WsAccountLeaf.Data source ws root heap nibs)
    (values : TrieWalk.Values data.graph valueLimit (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad heap 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad heap query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad heap query)
    (rootProtection : Keccak256.Protected stp pad heap (ws+24#64))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (room : heap.toNat+32≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word addr)])
    (tailCost : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "ws_get_account_optional") arguments continuation)).2.clock≤191*valueLimit+tailPrice+2594 := by
  obtain ⟨callee,called,addressCell⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "ws_get_account_optional") "addr" body addr
    (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  let entryData := WsAccountLeaf.Data.of_fields source entry ws root heap nibs data rfl rfl rfl rfl rfl
  let entryValues := TrieWalk.Values.rebase source.memory entry.memory source.memaddrs entry.memaddrs data.graph valueLimit values rfl rfl
  have entryHash := Keccak256.EntryData.of_fields source entry stp addr pad heap 20 rfl rfl rfl rfl rfl hashData
  have cost := body_cost entry ws root addr heap nibs stp pad cursor limit cutoff valueLimit entryData entryValues protectedValues entryHash
    graphProtection valueProtection rootProtection addressCell (Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl)
    heapGlobal room heapLower heapAligned sizeBound aligned scratchBelow installed
  have total := Input.ClockCost.scoped_current source name .one (ofString "ws_get_account_optional") arguments _ body continuation callee .one
    (191*valueLimit+2593) tailPrice args called cost tailCost
  omega

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.scoped_cost
