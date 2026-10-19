import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Value
import InitECandidate.Solver.Input.ScopedCallData

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

theorem lookup_known (code) (installed : Input.OriginalCode.Installed code) (s1 n1 s2 n2 : U256Value.Words)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite code.lookup (ofString "extend_memory_cost2")
      [U256Value.tuple s1, U256Value.tuple n1, U256Value.tuple s2, U256Value.tuple n2] = some (actual, callee, shape)) :
    actual = body ∧ callee.lookup (ofString "s1") = some (U256Value.tuple s1) ∧
      callee.lookup (ofString "n1") = some (U256Value.tuple n1) ∧ callee.lookup (ofString "s2") = some (U256Value.tuple s2) ∧
      callee.lookup (ofString "n2") = some (U256Value.tuple n2) := by
  have raw := lookupCodeHOLFinite_eq_some code.lookup (ofString "extend_memory_cost2") _ actual callee shape called
  simp only [lookupCodeHOLExact, original_code code installed] at raw
  split at raw
  · have same := Option.some.inj raw
    have bodyEq := congrArg Prod.fst same
    have s1Eq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "s1")) same
    have n1Eq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "n1")) same
    have s2Eq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "s2")) same
    have n2Eq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "n2")) same
    exact ⟨bodyEq.symm, by simpa [ofString] using s1Eq.symm, by simpa [ofString] using n1Eq.symm,
      by simpa [ofString] using s2Eq.symm, by simpa [ofString] using n2Eq.symm⟩
  · cases raw

set_option maxHeartbeats 1000000 in
theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (s1 n1 s2 n2 : U256Value.Words) (view : MemoryExpansionCost.View source frame current)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (argsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [U256Value.tuple s1, U256Value.tuple n1, U256Value.tuple s2, U256Value.tuple n2])
    (run : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "extend_memory_cost2") arguments continuation) = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 43 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current)) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, value, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name pairShape (ofString "extend_memory_cost2") arguments continuation returned run
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨bodyEq, start1, size1, start2, size2⟩ := lookup_known source.code view.installed s1 n1 s2 n2 actual callee shape called
  rw [bodyEq] at bodyRun
  have entryView : MemoryExpansionCost.View (callEntryStateHOLFinite source callee) frame current := view.after_erase rfl
  obtain ⟨valueEq, bodyPaid, bound, funded, clock, memory, fields⟩ :=
    normal (callEntryStateHOLFinite source callee) target frame current s1 n1 s2 n2 entryView start1 size1 start2 size2 value bodyRun
  change bodyPaid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - bodyPaid at clock
  have targetClock : target.clock = source.clock - (bodyPaid + 1) := by rw [clock]; omega
  have frameEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) fields
  change {target with locals := source.locals} = {source with clock := target.clock} at frameEq
  have next : Input.CallNormal.continuationEntry source target name value = setVarHOLFinite (ofString name)
      (MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current)) {source with clock := source.clock - (bodyPaid + 1)} := by
    change setVarHOLFinite (ofString name) value {target with locals := source.locals} = _
    rw [valueEq, frameEq, targetClock]
  let ready := setVarHOLFinite (ofString name) (MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current)) {source with clock := source.clock - (bodyPaid + 1)}
  refine ⟨bodyPaid + 1, ready, inner, by omega, by omega, by omega, rfl, rfl, ?_, postEq⟩
  rw [next] at tailRun
  exact tailRun

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.lookup_known
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.normal_prefix
