import InitECandidate.Solver.Rlp.ListCountIgnoredFrame
namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ignored_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_list_count") arguments)=(none,post)) :
    post.locals=source.locals ∧ Validation.Arena post cursor limit := by
  obtain ⟨locals,nextArena,above⟩ := ignored_normal_above source post pointer length cursor limit arguments args arena fits installed normal
  exact ⟨locals,nextArena⟩

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.ignored_normal
