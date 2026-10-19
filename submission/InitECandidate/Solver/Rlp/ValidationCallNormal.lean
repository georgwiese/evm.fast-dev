import InitECandidate.Solver.Rlp.ValidationCallFrame
namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real normal ignored caller restores its own locals and receives the
original arena, with the caller cost derived from the actual execution. -/
theorem ignored_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") arguments)=(none,post)) :
    1≤source.clock ∧ post.locals=source.locals ∧ Validation.Arena post cursor limit ∧
      source.clock-post.clock≤14*(2*length.toNat+1)+5 := by
  obtain ⟨positive,locals,nextArena,above,priced⟩ := ignored_normal_above source post pointer length cursor limit arguments args arena fits installed normal
  exact ⟨positive,locals,nextArena,priced⟩

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.ignored_normal
