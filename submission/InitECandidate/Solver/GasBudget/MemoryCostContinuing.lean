import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls
import InitECandidate.Solver.Input.KnownUnaryContinuing

namespace InitECandidate.Solver.GasBudget.MemoryCostCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem continuing (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (expression : ExpHOL 64) (continuation : ProgHOL 64) (argument : Argument kind)
    (installed : Input.OriginalCode.Installed source.code)
    (read : WitnessRadix.QueryBranch.eval source expression = some (kind.input argument))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one kind.name [expression] continuation) = (none, post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ kind.price + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (kind.result argument) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (none, inner) ∧ post = WitnessRadix.QueryBranch.restore source name inner := by
  exact Input.KnownUnaryPrefix.continuing source post name .one kind.name kind.formal kind.argumentShape .one kind.body kind.price expression continuation
    (kind.input argument) (kind.result argument) (original_code kind source.code installed) (pure_body kind source.code installed)
    (price_body kind source.code installed) read (determines kind source.code installed argument) run

end InitECandidate.Solver.GasBudget.MemoryCostCalls

#print axioms InitECandidate.Solver.GasBudget.MemoryCostCalls.continuing
