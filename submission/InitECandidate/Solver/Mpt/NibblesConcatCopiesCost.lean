import InitECandidate.Solver.Mpt.NibblesConcatCopies
import InitECandidate.Solver.WitnessRadix.CopyGeneralCost
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All outcomes of both actual copies, charged by their original word
loops and at most seven tail bytes each. The second call is priced only
after the first really falls through. -/
theorem copies_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (sourceA : AllocatedBytes.Arena a al.toNat) (sourceB : AllocatedBytes.Arena b bl.toNat)
    (destination : AllocatedBytes.Arena heap (al.toNat+bl.toNat))
    (aCell : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (alCell : source.locals.lookup (ofString "al")=some (.val (.word al)))
    (bCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (blCell : source.locals.lookup (ofString "bl")=some (.val (.word bl)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterAllocation).2.clock≤al.toNat/8+bl.toNat/8+16 := by
  have addition : (heap+al).toNat=heap.toNat+al.toNat:=BitVec.toNat_add_of_lt (by have upper:=destination.upper; omega)
  have firstArena:=destination.weaken heap (al.toNat+bl.toNat) al.toNat (by omega)
  have secondArena : AllocatedBytes.Arena (heap+al) bl.toNat:=⟨by rw [addition]; have lower:=destination.lower; omega,
    by rw [addition]; have upper:=destination.upper; omega⟩
  have firstArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) firstArguments=some (CopyGeneral.values heap a al.toNat):=by
    simp [firstArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,aCell,alCell,outCell]
  have firstMapped:=AllocatedBytes.copy_mapped source a heap al.toNat domain sourceA firstArena
  have firstSmall : al.toNat+32<2^64:=by have upper:=sourceA.upper; omega
  have firstPrice:=CopyGeneral.call_cost_blocks source firstArguments a heap al.toNat firstArgs (CopyGeneral.original_code source.code installed) firstMapped firstSmall
  rw [body_shapes.2.1]
  have result:=Input.ClockCost.sequence_reached_current source firstCopy afterFirst (al.toNat/8+8) (bl.toNat/8+8) firstPrice (by
    intro middle normal
    obtain ⟨_funded,_cost,middleEq⟩:=CopyGeneral.call_normal source middle firstArguments a heap al.toNat firstArgs (CopyGeneral.original_code source.code installed) firstMapped firstSmall normal
    rw [middleEq]
    let first:=CopyGeneral.callState source a heap al.toNat
    have secondArgs : evalListHOLFinite first (h:=fun query=>Classical.propDecidable (first.memaddrs query)) secondArguments=some (CopyGeneral.values (heap+al) b bl.toNat):=by
      simp [secondArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,first,CopyGeneral.callState,bCell,blCell,alCell,outCell,
        valueIsWord,valueWord,wordOpHOL,wordOp]
    have secondPrice:=CopyGeneral.call_cost_blocks first secondArguments b (heap+al) bl.toNat secondArgs (CopyGeneral.original_code source.code installed)
      (AllocatedBytes.copy_mapped first b (heap+al) bl.toNat domain sourceB secondArena) (by have upper:=sourceB.upper; omega)
    rw [body_shapes.2.2.1]
    have footerPrice : Input.ClockCost.Bound first.code footer 0:=by rw [body_shapes.2.2.2]; exact Input.ClockCost.returned first.code _
    simpa only [Nat.add_zero] using Input.ClockCost.sequence_current first secondCopy footer (bl.toNat/8+8) 0 secondPrice footerPrice)
  omega

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.copies_cost
