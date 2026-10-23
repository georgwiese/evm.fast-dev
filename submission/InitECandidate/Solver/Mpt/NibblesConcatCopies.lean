import InitECandidate.Solver.Mpt.NibblesConcatProgram
import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def copied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64):=
  CopyGeneral.callState (CopyGeneral.callState source a heap al.toNat) b (heap+al) bl.toNat

/-- Invert both genuine ignored memcpy calls and the actual footer. Their
complete memory effects, caller bindings and source clocks are derived
from normal execution, with mapping supplied by real physical extents. -/
theorem copies_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (sourceA : AllocatedBytes.Arena a al.toNat) (sourceB : AllocatedBytes.Arena b bl.toNat)
    (destination : AllocatedBytes.Arena heap (al.toNat+bl.toNat))
    (aCell : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (alCell : source.locals.lookup (ofString "al")=some (.val (.word al)))
    (bCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (blCell : source.locals.lookup (ofString "bl")=some (.val (.word bl)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterAllocation=(some (.returned value),target)) :
    value=.val (.word heap) ∧ target=emptyLocalsHOLFinite (copied source heap a al b bl) := by
  have addition : (heap+al).toNat=heap.toNat+al.toNat:=BitVec.toNat_add_of_lt (by have upper:=destination.upper; omega)
  have firstArena:=destination.weaken heap (al.toNat+bl.toNat) al.toNat (by omega)
  have secondArena : AllocatedBytes.Arena (heap+al) bl.toNat:=⟨by rw [addition]; have lower:=destination.lower; omega,
    by rw [addition]; have upper:=destination.upper; omega⟩
  have firstArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) firstArguments=some (CopyGeneral.values heap a al.toNat):=by
    simp [firstArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,aCell,alCell,outCell]
  have firstSafe : Input.LocalPrefix (ofString "out") firstCopy:=.call none _ _ (by intro name impossible; cases impossible)
  rw [body_shapes.2.1] at normal
  obtain ⟨middle,firstRun,continued,_out⟩:=firstSafe.normal_continue source target afterFirst value normal
  obtain ⟨_funded,_cost,middleEq⟩:=CopyGeneral.call_normal source middle firstArguments a heap al.toNat firstArgs (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped source a heap al.toNat domain sourceA firstArena) (by have upper:=sourceA.upper; omega) firstRun
  rw [middleEq] at continued
  let first:=CopyGeneral.callState source a heap al.toNat
  have secondArgs : evalListHOLFinite first (h:=fun query=>Classical.propDecidable (first.memaddrs query)) secondArguments=some (CopyGeneral.values (heap+al) b bl.toNat):=by
    simp [secondArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,first,CopyGeneral.callState,bCell,blCell,alCell,outCell,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have secondSafe : Input.LocalPrefix (ofString "out") secondCopy:=.call none _ _ (by intro name impossible; cases impossible)
  rw [body_shapes.2.2.1] at continued
  obtain ⟨last,secondRun,footerRun,_out⟩:=secondSafe.normal_continue first target footer value continued
  obtain ⟨_funded,_cost,lastEq⟩:=CopyGeneral.call_normal first last secondArguments b (heap+al) bl.toNat secondArgs (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped first b (heap+al) bl.toNat domain sourceB secondArena) (by have upper:=sourceB.upper; omega) secondRun
  rw [lastEq,body_shapes.2.2.2] at footerRun
  obtain ⟨read,endpoint⟩:=Input.return_normal (copied source heap a al b bl) target (localVar "out") value footerRun
  have expected : eval (copied source heap a al b bl) (localVar "out")=some (.val (.word heap)):=by
    simp [eval,evalHOLExact,toExact,localVar,copied,CopyGeneral.callState,outCell]
  exact ⟨Option.some.inj (read.symm.trans expected),endpoint⟩

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.copies_normal
