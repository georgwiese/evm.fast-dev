import InitECandidate.Solver.Rlp.ItemTotalFrame
namespace InitECandidate.Solver.Rlp.ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem check_safe : Input.LocalPrefix (ofString "h") check := check_safe_frame

theorem after_header_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+header.toNat+payload.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterHeader=(some (.returned value),target)) :
    value=.val (.word (header+payload)) ∧ Validation.Arena target cursor limit := by
  obtain ⟨same,nextArena,above⟩ := after_header_normal_above source target pointer header payload flag cursor limit pointerCell headerCell arena fits installed value normal
  exact ⟨same,nextArena⟩

/-- Actual normal item totals are positive and bounded by the passed
remaining length. The returned total also bounds this body's observed cost,
which permits linear amortization across a real list traversal. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ totalWord : BitVec 64,value=.val (.word totalWord) ∧ 1≤totalWord.toNat ∧ totalWord.toNat≤length.toNat ∧
      Validation.Arena target cursor limit ∧ source.clock-target.clock≤28*totalWord.toNat+30 := by
  obtain ⟨totalWord,same,positive,bounded,nextArena,above,priced⟩ := body_normal_above source target pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  exact ⟨totalWord,same,positive,bounded,nextArena,priced⟩

end InitECandidate.Solver.Rlp.ItemTotal

#print axioms InitECandidate.Solver.Rlp.ItemTotal.check_safe
#print axioms InitECandidate.Solver.Rlp.ItemTotal.after_header_normal
#print axioms InitECandidate.Solver.Rlp.ItemTotal.body_normal
