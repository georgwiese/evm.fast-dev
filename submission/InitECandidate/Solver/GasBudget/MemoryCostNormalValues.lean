import InitECandidate.Solver.GasBudget.WordsOfValue
import InitECandidate.Solver.Input.PureNormal

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem Ceil32.normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (v : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString "v") = some (.val (.word v))) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Ceil32.body = (some (.returned returned), post)) :
    returned = .val (.word (Ceil32.resultWord v)) ∧ Ceil32.price v ≤ source.clock ∧ post.clock = source.clock - Ceil32.price v ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - Ceil32.price v} := by
  apply Input.PureNormal.from_funded source post Ceil32.body (Ceil32.price v) _ returned normal
  intro entry locals code enough
  exact Ceil32.execute entry v (by rw [code]; exact installed) (by rw [locals]; exact binding) enough

theorem WordsOf.normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (binding : source.locals.lookup (ofString "n") = some (.val (.word n))) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source WordsOf.body = (some (.returned returned), post)) :
    returned = .val (.word (WordsOf.resultWord n)) ∧ WordsOf.price n ≤ source.clock ∧ post.clock = source.clock - WordsOf.price n ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - WordsOf.price n} := by
  apply Input.PureNormal.from_funded source post WordsOf.body (WordsOf.price n) _ returned normal
  intro entry locals code enough
  exact WordsOf.execute entry n (by rw [code]; exact installed) (by rw [locals]; exact binding) enough

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.Ceil32.normal
#print axioms InitECandidate.Solver.GasBudget.WordsOf.normal
