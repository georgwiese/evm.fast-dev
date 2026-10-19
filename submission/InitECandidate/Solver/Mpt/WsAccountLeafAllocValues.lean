import InitECandidate.Solver.Mpt.WsAccountLeafHashValues
import InitECandidate.Solver.Mpt.WsAccountLeafAllocCost
import InitECandidate.Solver.Mpt.TrieWalkValuesRebase
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {property : BitVec 64 → BitVec 64 → Prop}

set_option maxRecDepth 100000 in
theorem trap_original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "trap_with")=some (Input.Trap.formals,Input.Trap.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 0 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_trap_with) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Input.Trap.body,Input.Trap.formals,
    Guest.guestFn_trap_with,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
/-- Normal allocation derives room for the actual fixed request. The real
continuation receives its allocated pointer and preserved entry value model. -/
theorem after_mark_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
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
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) :
    h.toNat+32≤33806089496 ∧ TrieWalk.Answer post.memaddrs valueLimit (property:=property) returned := by
  classical
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "h" [.const 32#64] afterAlloc h 32#64 args
    (alloc_original_code source.code installed) (trap_original_code source.code installed) heap heapBound returned normal
  change h.toNat+32≤33806089496 at room
  let ready := bind (PersistentAlloc.post {source with clock := source.clock-1} h 32#64) "h" h
  have otherGlobal (name : String) (different : ofString "heap_ptr"≠ofString name) :
      ready.globals.lookup (ofString name)=source.globals.lookup (ofString name) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded h 32#64)))).lookup (ofString name)=_
    simp [HolFiniteMapExact.update,FUPDATE,different]
  let readyData := Data.of_fields source ready ws root h nibs data rfl rfl rfl (otherGlobal "ws" (by decide)) (otherGlobal "mpt_nib_scratch" (by decide))
  have readyHashData := Keccak256.EntryData.of_fields source ready stp addr pad h 20 rfl rfl rfl
    (otherGlobal "keccak_st" (by decide)) (otherGlobal "keccak_pad" (by decide)) hashData
  let readyValues : TrieWalk.Values readyData.graph valueLimit property := TrieWalk.Values.rebase source.memory ready.memory source.memaddrs ready.memaddrs data.graph valueLimit values rfl rfl
  have readyValueProtection : TrieWalk.ValueProtected readyData.graph nibs := protectedValues
  have readyGraphProtection : ∀ query,readyData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have readyHashValueProtection : ∀ query,TrieWalk.ValueFootprint readyData.graph query → Keccak256.Protected stp pad h query := valueProtection
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word addr)) :=
    (bind_lookup_other _ "h" "addr" h (by decide)).trans addressCell
  have readyOutput : ready.locals.lookup (ofString "h")=some (.val (.word h)) := bind_lookup_same _ _ _
  have answer := after_alloc_normal_value ready inner ws root addr h nibs stp pad readyData valueLimit readyValues readyValueProtection readyHashData
    readyGraphProtection readyHashValueProtection rootProtection readyAddress readyOutput installed returned tailRun
  exact ⟨room,by rw [restored]; exact answer⟩

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.trap_original_code
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_mark_normal_value
