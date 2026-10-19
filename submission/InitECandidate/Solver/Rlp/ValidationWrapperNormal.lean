import InitECandidate.Solver.Rlp.ValidationWrapperFrame
namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The public original wrapper's real normal return restores its saved
scratch cursor and retains the frame cursor and ordinary bounded arena. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ Validation.Arena target cursor limit := by
  obtain ⟨same,nextArena,above⟩ := body_normal_above source target pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  exact ⟨same,nextArena⟩

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.body_normal
