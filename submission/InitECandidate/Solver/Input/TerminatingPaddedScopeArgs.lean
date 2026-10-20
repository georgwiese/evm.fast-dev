import InitECandidate.Solver.Input.CallResume
import InitECandidate.Solver.Input.EvaluationClockSub
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem lower_call_entry {F : Type} (source : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (padding : Nat) (positive : 1 ≤ source.clock) :
    {callEntryStateHOLFinite {source with clock := source.clock + padding} callee with
      clock := (callEntryStateHOLFinite {source with clock := source.clock + padding} callee).clock - padding} = callEntryStateHOLFinite source callee := by
  change {source with locals := callee,clock := source.clock + padding - 1 - padding} = {source with locals := callee,clock := source.clock - 1}
  rw [show source.clock + padding - 1 - padding = source.clock - 1 by omega]

/-- A real padded callee return determines the actual tuple/scalar
binding and continuation of any enclosing non-timeout run. Funding follows
from that run; all memory and FFI effects are the actual callee effects. -/
theorem terminating_padded_scope_args {F : Type} (source post middle : PanSemStateFiniteExact 64 F)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body continuation : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (value : ValueHOL 64) (padding : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body,callee,returnShape))
    (paddingPositive : 1 ≤ padding)
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite {source with clock := source.clock + padding} callee) body = (some (.returned value),middle))
    (shapePass : (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) returnShape) = true)
    (result : Option (PanSemResultExact 64))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    padding ≤ middle.clock ∧ 1 ≤ source.clock ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned value),{middle with clock := middle.clock - padding}) ∧
      ∃ target,evaluateHOLFiniteState (CallNormal.continuationEntry source {middle with clock := middle.clock - padding} name value) continuation = (result,target) ∧
        post = WitnessRadix.QueryBranch.restore source name target := by
  have positive : 1 ≤ source.clock := by
    by_contra bad
    have zero : source.clock = 0 := by omega
    have stopped : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (some .timeOut,emptyLocalsHOLFinite source) := by
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      simp only [args,called,if_pos zero]
    have same := congrArg Prod.fst (stopped.symm.trans normal)
    exact notTimeout same.symm
  let padded := {source with clock := source.clock + padding}
  have scopeRun := CallNormal.return_execute padded middle name shape function arguments values body continuation callee returnShape value (by dsimp only [padded]; rw [EvaluateClockSubCall.evalList_upd_clock]; exact args) called
    (by change 1 ≤ source.clock + padding; omega) bodyRun shapePass
  have whole := panPropsEvaluateAddClockEq (.decCall (ofString name) shape function arguments continuation) source result post padding ⟨normal,notTimeout⟩
  change evaluateHOLFiniteState padded (.decCall (ofString name) shape function arguments continuation) = _ at whole
  rw [scopeRun] at whole
  let continued := CallNormal.continuationEntry padded middle name value
  have endClock : (evaluateHOLFiniteState continued continuation).2.clock = post.clock + padding := by
    have h := congrArg (fun output => output.2.clock) whole
    exact h
  have nextClock := evaluateHOLFiniteState_clock_le continued continuation
  have enough : padding ≤ middle.clock := by change (evaluateHOLFiniteState continued continuation).2.clock ≤ middle.clock at nextClock; omega
  have lowered := evaluation_clock_sub (callEntryStateHOLFinite padded callee) middle body (some (.returned value)) padding bodyRun enough (by intro impossible; cases impossible)
  rw [lower_call_entry source callee padding positive] at lowered
  have resumed := CallNormal.return_execute source {middle with clock := middle.clock - padding} name shape function arguments values body continuation callee returnShape value args called positive lowered shapePass
  rw [resumed] at normal
  let current := CallNormal.continuationEntry source {middle with clock := middle.clock - padding} name value
  let target := (evaluateHOLFiniteState current continuation).2
  have actualResult : (evaluateHOLFiniteState current continuation).1 = result := congrArg Prod.fst normal
  have actual : evaluateHOLFiniteState current continuation = (result,target) := Prod.ext actualResult rfl
  have restore : post = WitnessRadix.QueryBranch.restore source name target := (congrArg Prod.snd normal).symm
  exact ⟨enough,positive,lowered,target,actual,restore⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.terminating_padded_scope_args
