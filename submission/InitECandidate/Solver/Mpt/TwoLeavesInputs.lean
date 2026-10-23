import InitECandidate.Solver.Mpt.TwoLeavesProgram

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure SideInputs (source : PanSemStateFiniteExact 64 Guest.HostMemory) (second : Bool) (key length pointer size : BitVec 64) : Prop where
  keyCell : source.locals.lookup (ofString (label second "k1" "k2"))=some (.val (.word key))
  lengthCell : source.locals.lookup (ofString (label second "l1" "l2"))=some (.val (.word length))
  pointerCell : source.locals.lookup (ofString (label second "v1" "v2"))=some (.val (.word pointer))
  sizeCell : source.locals.lookup (ofString (label second "vl1" "vl2"))=some (.val (.word size))

theorem SideInputs.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (second : Bool) (key length pointer size : BitVec 64)
    (inputs : SideInputs source second key length pointer size) (localsEq : target.locals=source.locals) : SideInputs target second key length pointer size := by
  exact ⟨by rw [localsEq]; exact inputs.keyCell,by rw [localsEq]; exact inputs.lengthCell,
    by rw [localsEq]; exact inputs.pointerCell,by rw [localsEq]; exact inputs.sizeCell⟩

theorem SideInputs.after_branch (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (second : Bool) (key length pointer size branch : BitVec 64)
    (inputs : SideInputs source second key length pointer size)
    (localsEq : target.locals=source.locals.update (ofString "br",.val (.word branch))) : SideInputs target second key length pointer size := by
  cases second <;> constructor
  all_goals rw [localsEq]
  all_goals first
    | simpa [HolFiniteMapExact.update,FUPDATE,label,ofString] using inputs.keyCell
    | simpa [HolFiniteMapExact.update,FUPDATE,label,ofString] using inputs.lengthCell
    | simpa [HolFiniteMapExact.update,FUPDATE,label,ofString] using inputs.pointerCell
    | simpa [HolFiniteMapExact.update,FUPDATE,label,ofString] using inputs.sizeCell

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.SideInputs.of_locals
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.SideInputs.after_branch
