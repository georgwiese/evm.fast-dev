import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls
import InitECandidate.Solver.Input.KnownUnaryException
import InitECandidate.Solver.GasBudget.MemoryCostNoException

namespace InitECandidate.Solver.GasBudget.U256Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (name : String) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (words : U256Value.Words) (identifier : MlS) (payload : ValueHOL 64)
    (read : eval source expression = some (U256Value.tuple words))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_is_zero") [expression] continuation) =
      (some (.exception identifier payload), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (.val (.word (resultWord words))) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source name inner := by
  exact Input.KnownUnaryPrefix.exception source post name .one (ofString "u256_is_zero") (ofString "a") U256Value.tupleShape .one body 0
    expression continuation (U256Value.tuple words) (.val (.word (resultWord words))) identifier payload (original_code source.code installed)
    (MemoryCostCalls.pure_body .zero source.code installed) (MemoryCostCalls.price_body .zero source.code installed) read
    (MemoryCostCalls.determines .zero source.code installed words) (MemoryCostEffects.safe_u256_is_zero source.code installed) run

end InitECandidate.Solver.GasBudget.U256Zero

#print axioms InitECandidate.Solver.GasBudget.U256Zero.exception_prefix
