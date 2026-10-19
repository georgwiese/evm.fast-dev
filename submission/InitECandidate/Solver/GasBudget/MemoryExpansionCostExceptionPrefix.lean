import InitECandidate.Solver.GasBudget.MemoryExpansionCostValue
import InitECandidate.Solver.Input.KnownBinaryException

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame current : BitVec 64) (start size : U256Value.Words) (view : View source frame current)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [U256Value.tuple start, U256Value.tuple size])
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) (.comb [.one, .one]) (ofString "extend_memory_cost1") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 21 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (pairValue (resultPair start size current)) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source name inner := by
  have code := MemoryCostEffects.entry source.code view.installed .extend_memory_cost1
  have codeKnown : source.code.lookup (ofString "extend_memory_cost1") = some
    ([(ofString "start", (.comb [.one, .one, .one, .one])), (ofString "size", (.comb [.one, .one, .one, .one]))], body, .comb [.one, .one]) := by
    simpa only [MemoryCostEffects.Kind.name, MemoryCostEffects.Kind.original, MemoryCostEffects.Kind.signature,
      Guest.guestFn_extend_memory_cost1, paramToHOL, shapeToHOL, List.map_cons, List.map_nil, body, MemoryCostEffects.Kind.body] using code
  apply Input.KnownBinaryPrefix.exception source post name (.comb [.one, .one]) (ofString "extend_memory_cost1")
    (ofString "start") (ofString "size") (.comb [.one, .one, .one, .one]) (.comb [.one, .one, .one, .one]) (.comb [.one, .one]) body 20 arguments continuation
    (U256Value.tuple start) (U256Value.tuple size) (pairValue (resultPair start size current)) identifier payload (by decide) codeKnown
    (MemoryCostEffects.pure_extend_memory_cost1 source.code view.installed)
    (MemoryCostEffects.price_extend_memory_cost1 source.code view.installed) args _ (MemoryCostEffects.safe_extend_memory_cost1 source.code view.installed) normal
  intro entry target value same fields left right run
  exact normal_value entry target frame current start size (view.after_erase fields) left right value run

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.exception_prefix
