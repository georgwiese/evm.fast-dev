import InitECandidate.Solver.Rlp.ValidationBodyFrame
namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal internal-validator return derives a real reached arena with
the same frame cursor and bounds, and returns the original scalar zero. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ ∃ nextCursor,Arena target nextCursor limit := by
  obtain ⟨same,nextCursor,nextArena,bounded,above⟩ := body_normal_above source target pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  exact ⟨same,nextCursor,nextArena⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.body_normal
