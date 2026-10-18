import InitECandidate.Solver.Input.ClockCostScoped
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.ScopedCallException
import InitECandidate.Solver.Input.NoException

namespace InitECandidate.Solver.Input.PricedReadOnlyPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (function : MlS) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL) (price : Nat)
    (code : source.code.lookup function = some (formals, body, shape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (positive : 1 ≤ source.clock)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (actual, callee, returnShape))
    (returned : ValueHOL 64) (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    ∃ paid, 1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      CallNormal.continuationEntry source target name returned = setVarHOLFinite (ofString name) returned {source with clock := source.clock - paid} := by
  have identified := LocalEffects.lookup_body source.code function formals body shape code values actual callee returnShape called
  rw [identified] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have fields := pureBody entry rfl
  rw [bodyRun] at fields
  change LocalEffects.erase target = LocalEffects.erase source at fields
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) fields
  have next := congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  have cost := priced entry rfl
  rw [bodyRun] at cost
  change source.clock - 1 - target.clock ≤ price at cost
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change target.clock ≤ source.clock - 1 at clock
  let paid := source.clock - target.clock
  have actualClock : target.clock = source.clock - paid := by dsimp only [paid]; omega
  refine ⟨paid, by dsimp only [paid]; omega, by dsimp only [paid]; omega, by dsimp only [paid]; omega, ?_⟩
  change CallNormal.continuationEntry source target name returned = setVarHOLFinite (ofString name) returned {source with clock := target.clock} at next
  simpa only [actualClock] using next

theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (declaredShape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL) (price : Nat)
    (code : source.code.lookup function = some (formals, body, returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.decCall (ofString name) declaredShape function arguments continuation) = (some (.returned value), post)) :
    ∃ paid returned inner, 1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := source.clock - paid}) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    CallNormal.scoped_data source post name declaredShape function arguments continuation value run
  obtain ⟨paid, nonzero, bound, fits, next⟩ := resume source target name function formals body returnShape price code pureBody priced positive
    values actual callee shape called returned bodyRun
  exact ⟨paid, returned, inner, nonzero, bound, fits, by rw [← next]; exact tailRun, postEq⟩

/-- If the original read-only helper cannot throw, every real escaping
exception follows its actual checked return and bounded paid prefix. -/
theorem exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (declaredShape : ShapeHOL)
    (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL) (price : Nat)
    (code : source.code.lookup function = some (formals, body, returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (safe : NoException.Safe source.code body)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) declaredShape function arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ paid returned inner, 1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := source.clock - paid}) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    CallNormal.scoped_exception_data source post name declaredShape function arguments continuation identifier payload run
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    have identified := LocalEffects.lookup_body source.code function formals body returnShape code values actual callee shape called
    rw [identified] at bodyRun
    have impossible := safe (callEntryStateHOLFinite source callee) rfl identifier payload
    rw [bodyRun] at impossible
    exact (impossible rfl).elim
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    obtain ⟨paid, nonzero, bound, fits, next⟩ := resume source target name function formals body returnShape price code pureBody priced positive
      values actual callee shape called returned bodyRun
    exact ⟨paid, returned, inner, nonzero, bound, fits, by rw [← next]; exact tailRun, postEq⟩

end InitECandidate.Solver.Input.PricedReadOnlyPrefix

#print axioms InitECandidate.Solver.Input.PricedReadOnlyPrefix.resume
#print axioms InitECandidate.Solver.Input.PricedReadOnlyPrefix.normal
#print axioms InitECandidate.Solver.Input.PricedReadOnlyPrefix.exception
