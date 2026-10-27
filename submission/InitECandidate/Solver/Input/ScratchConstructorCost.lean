import InitECandidate.Solver.Input.ScratchClearCost
import InitECandidate.Solver.Input.ScratchConstructors
import InitECandidate.Solver.Input.ScratchFrame
import InitECandidate.Solver.Arenas.MarkCost

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every outcome of the literal current message constructor. -/
theorem ScratchConstructors.message_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64)
    (pointerBound : pointer.toNat ≤ InitE.scratchEnd) (ordered : limit ≤ pointer)
    (aligned : limit.toNat % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    source.clock - (evaluateHOLFiniteState source ScratchConstructors.messageBody).2.clock ≤ 4 := by
  rw [ScratchConstructors.message_shape]
  exact ScratchClear.allocated_clear_price source pointer limit 176 "m" (.return (localVar "m"))
    (by decide) (by decide) pointerBound ordered aligned domain installed pointerGlobal limitGlobal

/-- The two actual cursor snapshots add two ticks before the real failed
scratch clear. No stack, message read or later EVM operation is assumed. -/
theorem ScratchFrame.body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64)
    (pointerBound : pointer.toNat ≤ InitE.scratchEnd) (ordered : limit ≤ pointer)
    (aligned : limit.toNat % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    source.clock - (evaluateHOLFiniteState source ScratchFrame.body).2.clock ≤ 6 := by
  rw [ScratchFrame.body_shape]
  apply Arenas.mark_price_reached source .down "stack_mark" pointer ScratchFrame.afterScratchMark 5
    (ScratchFrame.mark_installed source.code installed .down) pointerGlobal
  let marked := bind {source with clock := source.clock - 1} "stack_mark" pointer
  change marked.clock - (evaluateHOLFiniteState marked ScratchFrame.afterScratchMark).2.clock ≤ 5
  rw [ScratchFrame.after_mark_shape]
  apply Arenas.mark_price_reached marked .up "mem_mark" limit ScratchFrame.afterMarks 4
    (ScratchFrame.mark_installed marked.code installed .up) limitGlobal
  let ready := bind {marked with clock := marked.clock - 1} "mem_mark" limit
  change ready.clock - (evaluateHOLFiniteState ready ScratchFrame.afterMarks).2.clock ≤ 4
  rw [ScratchFrame.after_marks_shape]
  exact ScratchClear.allocated_clear_price ready pointer limit 280 "e" ScratchFrame.afterClear
    (by decide) (by decide) pointerBound ordered aligned domain installed pointerGlobal limitGlobal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.ScratchConstructors.message_price
#print axioms InitECandidate.Solver.Input.ScratchFrame.body_price
