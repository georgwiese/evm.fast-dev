import InitECandidate.Solver.Rlp.ListCountBody
import InitECandidate.Solver.Input.ClockCostPotentialLoop

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem condition_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length offset word : BitVec 64)
    (offsetCell : source.locals.lookup (ofString "off")=some (.val (.word offset)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word word)))
    (nonzero : word≠0) : offset.toNat<length.toNat := by
  have actual : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=
      some (.val (.word (if offset.toNat<length.toNat then 1#64 else 0#64))) := by
    simp [evalHOLFinite,condition,evalHOLExact,localVar,toExact,offsetCell,lengthCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  by_contra inactive
  rw [if_neg inactive] at actual
  have zero : word=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans actual
  exact nonzero zero

/-- The unchanged list-count loop is linear in the passed byte length:
normal iterations pay from actual consumed bytes; an aborted final iteration
fits the remaining allowance. Nested validation is already included. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (valid : Invariant pointer length cursor limit source) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤allowance length source := by
  rw [loop_shape]
  apply Input.ClockCost.potential_loop source.code condition loopBody (Invariant pointer length cursor limit) (allowance length) ?_ source rfl valid
  intro current codeEq model word read nonzero funded
  obtain ⟨offset,count,view⟩ := model
  have active := condition_active current length offset word view.offsetCell view.lengthCell read nonzero
  let entry := decClockHOLFinite current
  have entryView := View.clock current pointer length cursor limit offset count view (current.clock-1)
  have currentInstalled : Input.OriginalCode.Installed entry.code := by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed
  have priced := loop_body_price entry pointer length cursor limit offset count entryView currentInstalled
  have bodyClock := evaluateHOLFiniteState_clock_le entry loopBody
  change current.clock-1-(evaluateHOLFiniteState entry loopBody).2.clock≤28*(length.toNat-offset.toNat)+31 at priced
  change (evaluateHOLFiniteState entry loopBody).2.clock≤current.clock-1 at bodyClock
  have currentAllowance := allowance_eq current length offset view.offsetCell
  dsimp only
  refine ⟨?_,?_⟩
  · change current.clock-(evaluateHOLFiniteState entry loopBody).2.clock≤allowance length current
    rw [currentAllowance]
    omega
  · intro continuing
    have actualNone : (evaluateHOLFiniteState entry loopBody).1=none :=
      continuing.resolve_right (loop_body_safe.summary_full entry).2.2.2
    obtain ⟨size,positive,bounded,nextView,number,normalPrice⟩ := loop_body_none entry (evaluateHOLFiniteState entry loopBody).2 pointer length cursor limit offset count entryView currentInstalled (Prod.ext actualNone rfl)
    refine ⟨⟨offset+size,count+1#64,nextView⟩,?_⟩
    change current.clock-(evaluateHOLFiniteState entry loopBody).2.clock+allowance length (evaluateHOLFiniteState entry loopBody).2≤allowance length current
    rw [allowance_eq _ length (offset+size) nextView.offsetCell,currentAllowance,number]
    change current.clock-1-(evaluateHOLFiniteState entry loopBody).2.clock≤59*size.toNat at normalPrice
    have remaining := BitVec.toNat_sub_of_le view.bounded
    rw [remaining] at bounded
    omega

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.condition_active
#print axioms InitECandidate.Solver.Rlp.ListCount.loop_cost
