import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ZeroAnyCost
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ScalarWordShape

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def branchSuffix : ProgHOL 64 := .seq
  (.store (.op .add [localVar "nd",.const 0#64]) (.const 3#64)) (.return (localVar "nd"))

set_option maxRecDepth 100000 in
private theorem branch_cost_tail_shape : tail .branch=
    .seq (.call (some (none,none)) (ofString "memzero") [localVar "nd",.const 176#64]) branchSuffix := by
  simp only [tail,body,original,Guest.Software.guestFn_node_new_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    branchSuffix,localVar,Option.map_none]

theorem branch_tail_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "nd")=some (.val (.word pointer)))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (tail .branch)).2.clock≤226 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "nd",.const 176#64]=
      some (Zero.values pointer 176) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,Zero.values]
  have zeroPrice:=ZeroAny.call_cost source _ pointer 176 (by decide) args (Zero.original_code source.code installed)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") [localVar "nd",.const 176#64])).2.clock≤226 at zeroPrice
  have footer : ClockCost.Bound source.code branchSuffix 0 :=
    ClockCost.sequence source.code _ _ 0 0 (ClockCost.store source.code _ _) (ClockCost.returned source.code _)
  rw [branch_cost_tail_shape]
  exact ClockCost.sequence_current source _ branchSuffix 226 0 zeroPrice footer

/-- The actual persistent branch constructor has a fixed all-outcome cost,
including its real176-byte clear, allocator traps and failed memory writes. -/
theorem branch_body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (body .branch)).2.clock≤228 := by
  obtain ⟨callee,called,nCell⟩ := PersistentAlloc.environment source.code.lookup 176#64 (PersistentAlloc.original_code source.code installed)
  rw [allocation_shape]
  apply ClockCost.scoped_reached_current source "nd" .one (ofString "alloc") [.const 176#64] _ PersistentAlloc.body (tail .branch) callee .one
    1 226 rfl called (PersistentAlloc.body_price source.code installed (callEntryStateHOLFinite source callee) rfl)
  intro target returned normal checked
  obtain ⟨pointer,answer⟩:=scalar_word_of_shape returned ((shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1)
  have currentInstalled : OriginalCode.Installed (CallNormal.continuationEntry source target "nd" returned).code :=
    OriginalCode.after_execution (callEntryStateHOLFinite source callee) target PersistentAlloc.body _ normal installed
  have pointerCell : (CallNormal.continuationEntry source target "nd" returned).locals.lookup (ofString "nd")=some (.val (.word pointer)) := by
    rw [←answer]
    exact CallNormal.continuation_lookup_same _ _ _ _
  exact branch_tail_price _ pointer pointerCell currentInstalled

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_tail_price
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_body_price
