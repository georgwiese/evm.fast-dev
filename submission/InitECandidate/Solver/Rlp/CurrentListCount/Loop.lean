import InitECandidate.Solver.Rlp.CurrentListCount.Body
import InitECandidate.Solver.Input.ClockCostPotentialLoop

namespace InitECandidate.Solver.Rlp.CurrentListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem condition_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length offset word : BitVec 64)
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) ListCount.condition=some (.val (.word word)))
    (nonzero : word≠0) : offset.toNat<length.toNat := by
  have actual : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) ListCount.condition=
      some (.val (.word (if offset.toNat<length.toNat then 1#64 else 0#64))) := by
    simp [evalHOLFinite,ListCount.condition,evalHOLExact,localVar,toExact,offsetCell,lengthCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  by_contra inactive
  rw [if_neg inactive] at actual
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans actual
  exact nonzero zero

/-- The real current list-count loop shares one remaining byte budget. Its
continuing iterations pay from the actual consumed item bytes; a stopped final
iteration fits the remaining allowance. All failures and clocks are included. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (valid : Invariant pointer length source) :
    source.clock-(evaluateHOLFiniteState source ListCount.loop).2.clock≤allowance length source := by
  rw [ListCount.loop_shape]
  apply ClockCost.potential_loop source.code ListCount.condition ListCount.loopBody (Invariant pointer length) (allowance length) ?_ source rfl valid
  intro current codeEq model word read nonzero funded
  obtain ⟨offset,count,view⟩ := model
  have active:=condition_active current length offset word view.offsetCell view.lengthCell read nonzero
  let entry:=decClockHOLFinite current
  have entryView:=view.at_clock (current.clock-1)
  have priced:=loop_body_price entry pointer length offset count entryView
  have bodyClock:=evaluateHOLFiniteState_clock_le entry ListCount.loopBody
  change current.clock-1-(evaluateHOLFiniteState entry ListCount.loopBody).2.clock≤14*(length.toNat-offset.toNat)+31 at priced
  change (evaluateHOLFiniteState entry ListCount.loopBody).2.clock≤current.clock-1 at bodyClock
  have currentAllowance:=view.allowance_eq
  dsimp only
  refine ⟨?_,?_⟩
  · change current.clock-(evaluateHOLFiniteState entry ListCount.loopBody).2.clock≤allowance length current
    rw [currentAllowance]
    omega
  · intro continuing
    have actualNone : (evaluateHOLFiniteState entry ListCount.loopBody).1=none := continuing.resolve_right (loop_body_safe.summary_full entry).2.2.2
    obtain ⟨size,positive,bounded,nextView,number,normalPrice,frame⟩ := loop_body_none entry (evaluateHOLFiniteState entry ListCount.loopBody).2 pointer length offset count entryView (Prod.ext actualNone rfl)
    refine ⟨⟨offset+size,count+1#64,nextView⟩,?_⟩
    change current.clock-(evaluateHOLFiniteState entry ListCount.loopBody).2.clock+allowance length (evaluateHOLFiniteState entry ListCount.loopBody).2≤allowance length current
    rw [nextView.allowance_eq,currentAllowance,number]
    change current.clock-1-(evaluateHOLFiniteState entry ListCount.loopBody).2.clock≤45*size.toNat at normalPrice
    have remaining:=BitVec.toNat_sub_of_le view.bounded
    rw [remaining] at bounded
    omega

end InitECandidate.Solver.Rlp.CurrentListCount

#print axioms InitECandidate.Solver.Rlp.CurrentListCount.condition_active
#print axioms InitECandidate.Solver.Rlp.CurrentListCount.loop_cost
