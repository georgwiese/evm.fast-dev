import InitECandidate.Solver.WitnessRadix.KeccakAnyBlocks
import InitECandidate.Solver.WitnessRadix.Keccak256AfterProgram
import InitECandidate.Solver.Input.BufferDynamicCost
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch Input Input.CounterFlow

def paddingFinish : ProgHOL 64 := .seq padFirst (.seq padLast (.seq absorbPad (.seq outProgram (.return (.const 0#64)))))

theorem output_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code outProgram 42 := by
  have words : ClockCost.Bound code outWords 0:=by
    apply ClockCost.of_quiet
    unfold outWords
    repeat' first | apply QuietClock.sequence | exact QuietClock.store code _ _
  have copy : ClockCost.Bound code outCopy 42:=by
    intro source codeEq
    exact BufferDynamicCost.copy_cost source (localVar "out") (localVar "stp") (.const 32#64) 32
      (by rw [codeEq]; exact installed) (by decide) rfl
  simpa only [outProgram,Nat.zero_max] using ClockCost.conditional code outAlignment outWords outCopy 0 42 words copy

theorem padding_finish_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code paddingFinish 61 := by
  have output : ClockCost.Bound code (.seq outProgram (.return (.const 0#64))) 42:=by
    simpa only [Nat.add_zero] using ClockCost.sequence code _ _ 42 0 (output_cost code installed) (ClockCost.returned code _)
  have absorb : ClockCost.Bound code (.seq absorbPad (.seq outProgram (.return (.const 0#64)))) 61:=
    ClockCost.sequence code _ _ 19 42 (KeccakAbsorb.call_cost code installed _) output
  have last : ClockCost.Bound code (.seq padLast (.seq absorbPad (.seq outProgram (.return (.const 0#64))))) 61:=by
    simpa only [padLast,Nat.zero_add] using ClockCost.sequence code _ _ 0 61 (ClockCost.of_quiet code _ (QuietClock.store_byte code _ _)) absorb
  simpa only [paddingFinish,padFirst,Nat.zero_add] using ClockCost.sequence code _ _ 0 61
    (ClockCost.of_quiet code _ (QuietClock.store_byte code _ _)) last

/-- Original padding and output on every outcome. The short remainder is
the actual block-loop exit value; no source or destination mapping is used. -/
theorem padding_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rem : Nat)
    (small : rem<136) (installed : OriginalCode.Installed source.code)
    (remCell : source.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem)))) :
    source.clock-(evaluateHOLFiniteState source paddingTail).2.clock≤408 := by
  have zero:=BufferDynamicCost.zero_cost source pad (.const 136#64) 136 installed (by decide) rfl
  have zeroPrice : source.clock-(evaluateHOLFiniteState source zeroPad).2.clock≤175:=zero
  change source.clock-(evaluateHOLFiniteState source (.seq zeroPad (.seq copyPad paddingFinish))).2.clock≤408
  apply ClockCost.sequence_reached_current source zeroPad _ 175 233 zeroPrice
  intro middle normal
  have codeEq:=(evaluation_fields source middle zeroPad none normal).2.2.2
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [codeEq]; exact installed
  have nextRem : middle.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem))):=
    (CallNormal.ignored_lookup source middle (ofString "rem") (ofString "memzero") [pad,.const 136#64] normal).trans remCell
  have remRead : eval middle (localVar "rem")=some (.val (.word (BitVec.ofNat 64 rem))):=by
    simp [eval,evalHOLExact,toExact,localVar,nextRem]
  have copy:=BufferDynamicCost.copy_cost middle pad (.op .add [localVar "p",localVar "i"]) (localVar "rem") rem
    nextInstalled (by omega) remRead
  have copyBound : CopyAny.price rem+1≤172:=by unfold CopyAny.price; omega
  have copyPrice : middle.clock-(evaluateHOLFiniteState middle copyPad).2.clock≤172:=copy.trans copyBound
  exact ClockCost.sequence_current middle copyPad paddingFinish 172 61 copyPrice (padding_finish_cost middle.code nextInstalled)

end InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.output_cost
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.padding_finish_cost
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.padding_cost
