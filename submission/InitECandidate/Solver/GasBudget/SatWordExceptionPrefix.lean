import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls
import InitECandidate.Solver.Input.KnownUnaryException

namespace InitECandidate.Solver.GasBudget.SatWord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (name : String) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (words : U256Value.Words) (identifier : MlS) (payload : ValueHOL 64)
    (read : eval source expression = some (U256Value.tuple words))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "sat_word") [expression] continuation) =
      (some (.exception identifier payload), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (.val (.word (resultWord words))) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source name inner := by
  exact Input.KnownUnaryPrefix.exception source post name .one (ofString "sat_word") (ofString "v") U256Value.tupleShape .one body 0
    expression continuation (U256Value.tuple words) (.val (.word (resultWord words))) identifier payload (original_code source.code installed)
    (MemoryCostCalls.pure_body .sat source.code installed) (MemoryCostCalls.price_body .sat source.code installed) read
    (MemoryCostCalls.determines .sat source.code installed words) (MemoryCostEffects.safe_sat_word source.code installed) run

end InitECandidate.Solver.GasBudget.SatWord

#print axioms InitECandidate.Solver.GasBudget.SatWord.exception_prefix
