import InitECandidate.Solver.Mpt.WitnessDecodeLookupProgram
import InitECandidate.Solver.Input.Copy32Bound
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def rootCopy : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy")
  [localVar "h",localVar "root_hash",.const 32#64]
def rootCache : ProgHOL 64 := .store (addConst (localVar "nd") 24#64) (localVar "h")
def cacheAllocated : ProgHOL 64 := .decCall (ofString "h") .one (ofString "alloc") [.const 32#64] (.seq rootCopy rootCache)
def cacheGuard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "nd") (.const 0#64)) cacheAllocated .skip

set_option maxRecDepth 100000 in
theorem suffix_shape : afterMaterialize = .seq cacheGuard (.return (localVar "nd")) := by
  simp only [afterMaterialize,materializeCall,afterLookup,lookupCall,afterCompare,body,
    Guest.guestFn_decode_witness_to_mpt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    cacheGuard,cacheAllocated,rootCopy,rootCache,localVar,addConst]
  rfl

/-- Actual allocator returns reinstall the caller's root hash and a typed
destination. No mapped read, write, or future allocator success is assumed. -/
theorem allocated_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root))) :
    source.clock-(evaluateHOLFiniteState source cacheAllocated).2.clock ≤ 44 := by
  obtain ⟨callee,called,length⟩ := PersistentAlloc.environment source.code.lookup 32#64
    (PersistentAlloc.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64) := rfl
  apply Input.ClockCost.scoped_reached_current source "h" .one (ofString "alloc") [.const 32#64] (PersistentAlloc.values 32#64)
    PersistentAlloc.body (.seq rootCopy rootCache) callee .one 1 42 args called
    (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl)
  intro target returned run checked
  cases returned with
  | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at checked
  | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at checked
  | val value =>
    cases value with
    | word destination =>
      let ready := Input.CallNormal.continuationEntry source target "h" (.val (.word destination))
      have readyH : ready.locals.lookup (ofString "h")=some (.val (.word destination)) := bind_lookup_same _ _ _
      have readyRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)) :=
        (bind_lookup_other {target with locals:=source.locals} "h" "root_hash" destination (by decide)).trans rootCell
      have codeEq := (Input.evaluation_fields (callEntryStateHOLFinite source callee) target PersistentAlloc.body _ run).2.2.2
      have readyInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
      have copyArgs : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address))
          [localVar "h",localVar "root_hash",.const 32#64]=some (CopyGeneral.values destination root 32) := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,readyH,readyRoot,CopyGeneral.values]
      exact Input.ClockCost.sequence_current ready rootCopy rootCache 42 0
        (Input.Copy32Flow.call_cost ready _ destination root copyArgs readyInstalled)
        (Input.ClockCost.store ready.code _ _)

theorem suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root))) :
    source.clock-(evaluateHOLFiniteState source afterMaterialize).2.clock ≤ 44 := by
  rw [suffix_shape]
  have guardCost := Input.ClockCost.conditional_current source (.cmp .notEqual (localVar "nd") (.const 0#64)) cacheAllocated .skip 44 0
    (allocated_cost source root installed rootCell) (Input.ClockCost.skip source.code source rfl)
  exact Input.ClockCost.sequence_current source cacheGuard (.return (localVar "nd")) 44 0 guardCost
    (Input.ClockCost.returned source.code _)

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.allocated_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.suffix_cost
