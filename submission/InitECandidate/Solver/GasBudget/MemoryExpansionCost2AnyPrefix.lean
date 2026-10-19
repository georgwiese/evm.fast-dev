import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Lookup
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Effects
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

/-- Only a completed normal cost2 call restores its temporary header write.
The four checked arguments are recovered from the actual lookup. -/
theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (view : MemoryExpansionCost.View source frame current) (name : String) (positive : 1 ≤ source.clock)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "extend_memory_cost2") values = some (actual, callee, shape))
    (returned : ValueHOL 64)
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    ∃ paid, 1 ≤ paid ∧ paid ≤ 43 ∧ paid ≤ source.clock ∧
      Input.CallNormal.continuationEntry source target name returned =
        setVarHOLFinite (ofString name) returned {source with clock := source.clock - paid} := by
  obtain ⟨s1, n1, s2, n2, valuesEq⟩ := lookup_shape source.code view.installed values actual callee shape called
  rw [valuesEq] at called
  obtain ⟨bodyEq, start1, size1, start2, size2⟩ := lookup_known source.code view.installed s1 n1 s2 n2 actual callee shape called
  rw [bodyEq] at bodyRun
  have entryView : MemoryExpansionCost.View (callEntryStateHOLFinite source callee) frame current := view.after_erase rfl
  obtain ⟨valueEq, bodyPaid, bound, funded, clock, memory, fields⟩ :=
    normal (callEntryStateHOLFinite source callee) target frame current s1 n1 s2 n2 entryView start1 size1 start2 size2 returned bodyRun
  change bodyPaid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - bodyPaid at clock
  have targetClock : target.clock = source.clock - (bodyPaid + 1) := by rw [clock]; omega
  have frameEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) fields
  change {target with locals := source.locals} = {source with clock := target.clock} at frameEq
  refine ⟨bodyPaid + 1, by omega, by omega, by omega, ?_⟩
  change setVarHOLFinite (ofString name) returned {target with locals := source.locals} = _
  rw [frameEq, targetClock]

theorem any_normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (view : MemoryExpansionCost.View source frame current) (name : String) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "extend_memory_cost2") arguments continuation) =
      (some (.returned value), post)) :
    ∃ paid returned inner, 1 ≤ paid ∧ paid ≤ 43 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := source.clock - paid}) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name pairShape (ofString "extend_memory_cost2") arguments continuation value run
  obtain ⟨paid, nonzero, bound, fits, next⟩ := resume source target frame current view name positive values actual callee shape called returned bodyRun
  exact ⟨paid, returned, inner, nonzero, bound, fits, by rw [← next]; exact tailRun, postEq⟩

theorem any_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (view : MemoryExpansionCost.View source frame current) (name : String) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "extend_memory_cost2") arguments continuation) =
      (some (.exception identifier payload), post)) :
    ∃ paid returned inner, 1 ≤ paid ∧ paid ≤ 43 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := source.clock - paid}) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name pairShape (ofString "extend_memory_cost2") arguments continuation identifier payload run
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    have identified := Input.LocalEffects.lookup_body source.code (ofString "extend_memory_cost2") _ body pairShape
      (original_code source.code view.installed) values actual callee shape called
    rw [identified] at bodyRun
    have impossible := safe source.code view.installed (callEntryStateHOLFinite source callee) rfl identifier payload
    rw [bodyRun] at impossible
    exact (impossible rfl).elim
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    obtain ⟨paid, nonzero, bound, fits, next⟩ := resume source target frame current view name positive values actual callee shape called returned bodyRun
    exact ⟨paid, returned, inner, nonzero, bound, fits, by rw [← next]; exact tailRun, postEq⟩

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.resume
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.any_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.any_exception_prefix
