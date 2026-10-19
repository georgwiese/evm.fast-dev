import InitECandidate.Solver.Mpt.WsAccountLeafHashCost
import InitECandidate.Solver.WitnessRadix.AllocationCall

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem alloc_original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 2 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_alloc) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,PersistentAlloc.body,PersistentAlloc.formals,
    Guest.guestFn_alloc,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Price the original temporary allocation and following hash/lookup
from current entry memory and room for its fixed32-byte request. -/
theorem after_mark_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws root addr h nibs stp pad : BitVec 64)
    (data : Data source ws root h nibs)
    (hashData : Keccak256.EntryData source stp addr pad h 20)
    (graphProtection : ∀ query,data.graph.Footprint query → Keccak256.Protected stp pad h query)
    (rootProtection : Keccak256.Protected stp pad h (ws+24#64))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word addr)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word h)))
    (room : h.toNat+32≤33806089496)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterMark).2.clock≤2296 := by
  classical
  by_cases zero : source.clock=0
  · omega
  have positive : 1≤source.clock := by omega
  let ready := bind (PersistentAlloc.post {source with clock := source.clock-1} h 32#64) "h" h
  have otherGlobal (name : String) (different : ofString "heap_ptr"≠ofString name) :
      ready.globals.lookup (ofString name)=source.globals.lookup (ofString name) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded h 32#64)))).lookup (ofString name)=_
    simp [HolFiniteMapExact.update,FUPDATE,different]
  let readyData := Data.of_fields source ready ws root h nibs data rfl rfl rfl (otherGlobal "ws" (by decide)) (otherGlobal "mpt_nib_scratch" (by decide))
  have readyHashData := Keccak256.EntryData.of_fields source ready stp addr pad h 20 rfl rfl rfl
    (otherGlobal "keccak_st" (by decide)) (otherGlobal "keccak_pad" (by decide)) hashData
  have readyGraphProtection : ∀ query,readyData.graph.Footprint query → Keccak256.Protected stp pad h query := graphProtection
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word addr)) :=
    (bind_lookup_other _ "h" "addr" h (by decide)).trans addressCell
  have readyOutput : ready.locals.lookup (ofString "h")=some (.val (.word h)) := bind_lookup_same _ _ _
  have priced := after_alloc_cost ready ws root addr h nibs stp pad readyData readyHashData readyGraphProtection rootProtection readyAddress readyOutput installed
  have monotone := evaluateHOLFiniteState_clock_le ready afterAlloc
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  have actual := PersistentAlloc.call_execute source "h" [.const 32#64] afterAlloc h 32#64 args (alloc_original_code source.code installed) heap room positive
  rw [afterMark,actual]
  change source.clock-(evaluateHOLFiniteState ready afterAlloc).2.clock≤2296
  change source.clock-1-(evaluateHOLFiniteState ready afterAlloc).2.clock≤2295 at priced
  change (evaluateHOLFiniteState ready afterAlloc).2.clock≤source.clock-1 at monotone
  omega

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.alloc_original_code
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_mark_cost
