import InitECandidate.Solver.Mpt.WsAccountLeafAllocValues
import InitECandidate.Solver.Mpt.WsAccountLeafCost

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {property : BitVec 64 → BitVec 64 → Prop}

set_option maxRecDepth 100000 in
/-- Complete original normal account-leaf lookup derives its allocation
room and actual binary/payload answer. The only cursor premise is its current
heap-end bound; no future allocation or helper outcome is supplied. -/
theorem body_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs) (valueLimit : Nat) (values : TrieWalk.Values data.graph valueLimit property)
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (heapBound : h.toNat≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    h.toNat+32≤33806089496 ∧ TrieWalk.Answer post.memaddrs valueLimit (property:=property) returned := by
  rw [body_shape] at normal
  have positive := Input.CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  let ready := bind {source with clock := source.clock-1} "mark" h
  let inner := (evaluateHOLFiniteState ready afterMark).2
  have actual := Input.HeapScope.mark_call_execute source h "mark" afterMark heap (Input.HeapScope.mark_original_code source.code installed) positive
  have joined := actual.symm.trans normal
  have resultEq := congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner) := Prod.ext resultEq rfl
  have postEq := (congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  let readyData := Data.of_fields source ready ws root h nibs data rfl rfl rfl rfl rfl
  let readyValues : TrieWalk.Values readyData.graph valueLimit property := TrieWalk.Values.rebase source.memory ready.memory source.memaddrs ready.memaddrs data.graph valueLimit values rfl rfl
  have readyValueProtection : TrieWalk.ValueProtected readyData.graph nibs := protectedValues
  have readyHashData := Keccak256.EntryData.of_fields source ready stp addr pad h 20 rfl rfl rfl rfl rfl hashData
  have readyGraphProtection : ∀ query,readyData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have readyHashValueProtection : ∀ query,TrieWalk.ValueFootprint readyData.graph query → Keccak256.Protected stp pad h query := valueProtection
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word addr)) :=
    (bind_lookup_other _ "mark" "addr" h (by decide)).trans addressCell
  obtain ⟨room,answer⟩ := after_mark_normal_value ready inner ws root addr h nibs stp pad readyData valueLimit readyValues readyValueProtection readyHashData
    readyGraphProtection readyHashValueProtection rootProtection readyAddress heap heapBound installed returned innerRun
  exact ⟨room,by rw [postEq]; exact answer⟩

set_option maxRecDepth 100000 in
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs) (valueLimit : Nat) (values : TrieWalk.Values data.graph valueLimit property)
    (protectedValues : TrieWalk.ValueProtected data.graph nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (valueProtection : ∀ query,TrieWalk.ValueFootprint data.graph query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (heapBound : h.toNat≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    h.toNat+32≤33806089496 ∧ TrieWalk.Answer post.memaddrs valueLimit (property:=property) returned ∧
      post.clock≤source.clock ∧ source.clock-2297≤post.clock := by
  obtain ⟨room,answer⟩ := body_normal_value source post ws root addr h nibs stp pad data valueLimit values protectedValues hashData
    graphProtection valueProtection rootProtection addressCell heap heapBound installed returned normal
  have cost := body_cost source ws root addr h nibs stp pad data hashData graphProtection rootProtection addressCell heap room installed
  have clock := evaluateHOLFiniteState_clock_le source body
  rw [normal] at cost clock
  exact ⟨room,answer,clock,by change source.clock-post.clock≤2297 at cost; omega⟩

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_normal_value
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_normal
