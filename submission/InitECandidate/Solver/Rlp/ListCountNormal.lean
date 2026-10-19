import InitECandidate.Solver.Rlp.ListCountNormalFrame
namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (valid : Invariant pointer length cursor limit source)
    (normal : evaluateHOLFiniteState source loop=(none,target)) : Invariant pointer length cursor limit target := by
  exact (loop_none_above source target pointer length cursor limit installed valid normal).1

/-- The original list counter returns an actual scalar count<=input length
and the original bounded arena, derived through every real normal iteration. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ countWord : BitVec 64,value=.val (.word countWord) ∧ countWord.toNat≤length.toNat ∧ Validation.Arena target cursor limit := by
  obtain ⟨countWord,same,bounded,nextArena,above⟩ := body_normal_above source target pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  exact ⟨countWord,same,bounded,nextArena⟩

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.loop_none
#print axioms InitECandidate.Solver.Rlp.ListCount.body_normal
