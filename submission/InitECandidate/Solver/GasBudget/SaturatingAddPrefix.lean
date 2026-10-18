import InitECandidate.Solver.GasBudget.SaturatingAdd
import InitECandidate.Solver.Input.ScalarPairLookup
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.SaturatingAdd
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (code : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "add_sat") values = some (actual, callee, returnShape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    ∃ a b, values = [.val (.word a), .val (.word b)] ∧
      Input.CallNormal.continuationEntry source target name returned = bind {source with clock := source.clock - 1} name (resultWord a b) := by
  obtain ⟨a, b, valuesEq, bodyEq, shapeEq, aCell, bCell⟩ :=
    Input.CallNormal.scalar_pair_lookup source.code.lookup _ AddExact.body code values actual callee returnShape called
  rw [bodyEq] at run
  obtain ⟨expected, actualRun, fields⟩ := execute (callEntryStateHOLFinite source callee) a b aCell bCell
  have resultEq := congrArg Prod.fst (run.symm.trans actualRun)
  have returnedEq : returned = .val (.word (resultWord a b)) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  have targetEq := congrArg Prod.snd (run.symm.trans actualRun)
  change target = expected at targetEq
  rw [← targetEq] at fields
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) fields
  change {target with locals := source.locals} = {source with clock := source.clock - 1} at callerFrame
  have next := congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  exact ⟨a, b, valuesEq, by simpa only [Input.CallNormal.continuationEntry, WitnessRadix.QueryBranch.bind, returnedEq] using next⟩

theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "add_sat") arguments continuation) = (some (.returned value), post)) :
    ∃ a b inner, 1 ≤ source.clock ∧
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word a), .val (.word b)] ∧
      a ≤ resultWord a b ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name (resultWord a b)) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name .one _ arguments continuation value run
  obtain ⟨a, b, valuesEq, next⟩ := resume source target name code values actual callee shape called returned bodyRun
  exact ⟨a, b, inner, positive, by rw [← valuesEq]; exact args, ge_left a b, by rw [← next]; exact tailRun, postEq⟩

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "add_sat") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ a b inner, 1 ≤ source.clock ∧
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word a), .val (.word b)] ∧
      a ≤ resultWord a b ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - 1} name (resultWord a b)) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name .one _ arguments continuation identifier payload run
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    obtain ⟨a, b, valuesEq, bodyEq, shapeEq, aCell, bCell⟩ :=
      Input.CallNormal.scalar_pair_lookup source.code.lookup _ AddExact.body code values actual callee shape called
    rw [bodyEq] at bodyRun
    obtain ⟨expected, actualRun, fields⟩ := execute (callEntryStateHOLFinite source callee) a b aCell bCell
    have impossible := congrArg Prod.fst (bodyRun.symm.trans actualRun)
    cases impossible
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    obtain ⟨a, b, valuesEq, next⟩ := resume source target name code values actual callee shape called returned bodyRun
    exact ⟨a, b, inner, positive, by rw [← valuesEq]; exact args, ge_left a b, by rw [← next]; exact tailRun, postEq⟩

end InitECandidate.Solver.GasBudget.SaturatingAdd

#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.resume
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.normal_prefix
#print axioms InitECandidate.Solver.GasBudget.SaturatingAdd.exception_prefix
