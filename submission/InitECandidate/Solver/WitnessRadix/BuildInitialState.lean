import InitECandidate.Solver.WitnessRadix.BuildInitialize

namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem entered_binding {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64) (entry : String × BitVec 64)
    (member : entry ∈ initialValues table count keys vals src dst) :
    (entered source table count keys vals src dst).locals.lookup (ofString entry.1) =
      some (.val (.word entry.2)) := by
  simp only [initialValues, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [entered, initialValues, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, ofString]

theorem entered_table {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64) :
    (entered source table count keys vals src dst).locals.lookup (ofString "t") = source.locals.lookup (ofString "t") := by
  simp [entered, initialValues, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]

theorem entered_count {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64) :
    (entered source table count keys vals src dst).locals.lookup (ofString "n") = source.locals.lookup (ofString "n") := by
  simp [entered, initialValues, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]

theorem entered_frame {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table count keys vals src dst : BitVec 64) :
    emptyLocalsHOLFinite (entered source table count keys vals src dst) = emptyLocalsHOLFinite source := by
  rfl

end InitECandidate.Solver.WitnessRadix.BuildEntry

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.entered_binding
#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.entered_frame
