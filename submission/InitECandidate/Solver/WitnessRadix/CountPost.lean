import InitECandidate.Solver.WitnessRadix.CountBody

namespace InitECandidate.Solver.WitnessRadix.CountProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem counter_frame {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64) :
    emptyLocalsHOLFinite (counterPost source digit zeros index) = emptyLocalsHOLFinite source := by
  unfold counterPost
  split <;> rfl

theorem counter_lookup {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64) (name : MlS)
    (notI : ofString "i" ≠ name) (notZeros : ofString "zeros" ≠ name) :
    (counterPost source digit zeros index).locals.lookup name = source.locals.lookup name := by
  by_cases zero : digit = 0#64
  all_goals simp [counterPost, zero, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, notI, notZeros]

theorem counter_other {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64) (name : String)
    (notI : ofString "i" ≠ ofString name) (notZeros : ofString "zeros" ≠ ofString name) :
    (counterPost source digit zeros index).locals.lookup (ofString name) =
      source.locals.lookup (ofString name) := by
  by_cases zero : digit = 0#64
  all_goals simp [counterPost, zero, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, notI, notZeros]

theorem counter_index {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64) :
    (counterPost source digit zeros index).locals.lookup (ofString "i") =
      some (.val (.word (index + 1#64))) := by
  simp [counterPost, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem counter_zeros {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64)
    (initial : source.locals.lookup (ofString "zeros") = some (.val (.word zeros))) :
    (counterPost source digit zeros index).locals.lookup (ofString "zeros") =
      some (.val (.word (if digit = 0#64 then zeros + 1#64 else zeros))) := by
  have notI : ofString "i" ≠ ofString "zeros" := by decide
  by_cases zero : digit = 0#64
  all_goals simp [counterPost, zero, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, notI, initial]

end InitECandidate.Solver.WitnessRadix.CountProgram

#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.counter_frame
