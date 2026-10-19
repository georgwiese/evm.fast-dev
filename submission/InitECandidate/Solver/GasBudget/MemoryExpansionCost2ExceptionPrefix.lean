import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Prefix
import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Effects
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

set_option maxHeartbeats 1000000 in
theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (s1 n1 s2 n2 : U256Value.Words) (view : MemoryExpansionCost.View source frame current)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (argsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [U256Value.tuple s1, U256Value.tuple n1, U256Value.tuple s2, U256Value.tuple n2])
    (run : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "extend_memory_cost2") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 43 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current)) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name pairShape (ofString "extend_memory_cost2") arguments continuation identifier payload run
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨bodyEq, start1, size1, start2, size2⟩ := lookup_known source.code view.installed s1 n1 s2 n2 actual callee shape called
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    rw [bodyEq] at bodyRun
    exact ((safe source.code view.installed) (callEntryStateHOLFinite source callee) rfl identifier payload (congrArg Prod.fst bodyRun)).elim
  · obtain ⟨value, inner, bodyRun, checked, tailRun, postEq⟩ := continued
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

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.exception_prefix
