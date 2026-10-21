import InitECandidate.Solver.Mpt.CompactToNibblesOdd
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_odd_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer out k : BitVec 64) (length : Nat)
    (positive : 1≤length) (small : length+4<2^64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (kCell : source.locals.lookup (ofString "k")=some (.val (.word k)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterOdd).2.clock≤length/4+4 := by
  have difference : BitVec.ofNat 64 length-1#64=BitVec.ofNat 64 (length-1):=BitVec.ofNat_sub_ofNat_of_le length 1 (by decide) positive
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) keyArguments=
      some (KeyToNibbles.anyValues (pointer+1#64) (BitVec.ofNat 64 (length-1)) (out+k)):=by
    simp [keyArguments,KeyToNibbles.anyValues,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,pointerCell,lengthCell,outCell,kCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  have priced:=KeyToNibbles.call_any_cost source (pointer+1#64) (out+k) (length-1) (by omega) (some none) keyArguments args installed
  have full:=Input.ClockCost.sequence_current source keyCall footer ((length-1)/4+4) 0 priced
    (Input.ClockCost.returned source.code resultExpression)
  exact full.trans (by omega)

/-- Price the actual optional nibble write and following generic original
converter, deriving its real scalar arguments only on normal passage. -/
theorem after_allocation_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer out odd : BitVec 64) (length : Nat)
    (positive : 1≤length) (small : length+4<2^64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterAllocation).2.clock≤length/4+4 := by
  let current:=QueryBranch.bind source "k" 0#64
  have currentPointer : current.locals.lookup (ofString "p")=some (.val (.word pointer)):=(bind_lookup_other source "k" "p" 0#64 (by decide)).trans pointerCell
  have currentLength : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=(bind_lookup_other source "k" "n" 0#64 (by decide)).trans lengthCell
  have currentOut : current.locals.lookup (ofString "out")=some (.val (.word out)):=(bind_lookup_other source "k" "out" 0#64 (by decide)).trans outCell
  have currentOdd : current.locals.lookup (ofString "odd")=some (.val (.word odd)):=(bind_lookup_other source "k" "odd" 0#64 (by decide)).trans oddCell
  have currentK : current.locals.lookup (ofString "k")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have firstCost : current.clock-(evaluateHOLFiniteState current oddGuard).2.clock≤0:=Input.ClockCost.of_quiet current.code oddGuard (odd_quiet current.code) current rfl
  have total:=Input.ClockCost.sequence_reached_current current oddGuard afterOdd 0 (length/4+4) firstCost (by
    intro middle normal
    obtain ⟨k,binary,kCell,nextPointer,nextLength,nextOut⟩:=odd_normal current middle pointer (BitVec.ofNat 64 length) out odd currentPointer currentLength currentOut currentOdd currentK normal
    have codeEq:=(Input.evaluation_fields current middle oddGuard none normal).2.2.2
    have nextInstalled : Input.OriginalCode.Installed middle.code:=by rw [codeEq]; exact installed
    exact after_odd_cost middle pointer out k length positive small nextPointer nextLength nextOut kCell nextInstalled)
  rw [after_allocation_shape]
  exact Input.ClockCost.declared_current source "k" (.const 0#64) 0#64 _ (length/4+4) rfl (by simpa only [Nat.zero_add] using total)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.after_odd_cost
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.after_allocation_cost
