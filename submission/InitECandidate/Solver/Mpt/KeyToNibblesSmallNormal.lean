import InitECandidate.Solver.Mpt.KeyToNibblesSmallExecution
import InitECandidate.Solver.Mpt.KeyToNibblesSpanAllocated
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A genuine variable-length normal conversion produces the actual nibble
view and precise write frame, without a supplied entry-clock allowance. -/
theorem small_body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (length : Nat) (small : length≤32)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (outputMapped : ∀ offset<2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (separate : ∀ left<length,∀ right<2*length,byteAddress key left≠byteAddress out right)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),target)) :
    returned=.val (.word 0#64) ∧ TrieWalk.KeyView target.memory target.memaddrs target.be out (2*length) ∧
      source.clock-target.clock≤length/4+3 ∧ SpanFrame source target out (2*length) := by
  let padding:=length+3
  let padded:={source with clock:=source.clock+padding}
  obtain ⟨post,run,view,cost,frame⟩:=small_execute_mapped padded key out length small keyCell outCell lengthCell little fits
    inputMapped outputMapped separate (by change length+3≤source.clock+padding; dsimp [padding]; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned returned)) target padding
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq:=congrArg Prod.fst (lifted.symm.trans run)
  have postEq:=congrArg Prod.snd (lifted.symm.trans run)
  change {target with clock:=target.clock+padding}=post at postEq
  have answer : returned=.val (.word 0#64):=by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq
  rw [←postEq] at view
  have actualCost:=body_any_cost source length (by omega) lengthCell
  rw [normal] at actualCost
  have actualFrame:=(body_span_frame source target out length (by omega) outCell lengthCell returned normal).2
  exact ⟨answer,view,actualCost,actualFrame⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_body_normal
