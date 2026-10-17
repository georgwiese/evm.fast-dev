import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem bind_lookup_same {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (word : BitVec 64) :
    (bind source name word).locals.lookup (ofString name) = some (.val (.word word)) := by
  simp [bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem bind_lookup_other {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name other : String) (word : BitVec 64) (different : ofString name ≠ ofString other) :
    (bind source name word).locals.lookup (ofString other) = source.locals.lookup (ofString other) := by
  simp [bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different]

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.bind_lookup_other
