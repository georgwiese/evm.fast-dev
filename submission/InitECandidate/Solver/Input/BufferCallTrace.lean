import InitECandidate.Solver.Input.TerminatingPrefixFunding
import InitECandidate.Solver.WitnessRadix.CopyGeneralCost
import InitECandidate.Solver.WitnessRadix.ZeroCost
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall

namespace InitECandidate.Solver.Input.BufferTrace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual original memcpy derives funding and its exact next state
from an observed non-timeout enclosing sequence. Later code may have any
outcome; source/destination validity is current mapped geometry only. -/
theorem copy_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (length : Nat) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (CopyGeneral.formals,Copy32.body,.one))
    (mapped : CopyContext.Mapped source src dst length) (small : length+32<2^64)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "memcpy") arguments) continuation)=(result,post))
    (notTimeout : result≠some .timeOut) :
    CopyGeneral.cost src dst length+1≤source.clock ∧
      evaluateHOLFiniteState (CopyGeneral.callState source src dst length) continuation=(result,post) := by
  let template := {source with memory:=CopyGeneral.resultMemory source.memory source.be src dst length}
  have execute (clock : Nat) (funded : CopyGeneral.cost src dst length+1≤clock) :
      evaluateHOLFiniteState {source with clock:=clock} (.call (some (none,none)) (ofString "memcpy") arguments)=
        (none,{template with clock:=clock-(CopyGeneral.cost src dst length+1)}) := by
    have currentArgs : evalListHOLFinite {source with clock:=clock} (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length) := by
      rw [EvaluateClockSubCall.evalList_upd_clock]
      exact args
    have currentMapped := CopyContext.Mapped.of_domain source {source with clock:=clock} src dst length rfl mapped
    exact CopyGeneral.call_execute {source with clock:=clock} arguments src dst length currentArgs code currentMapped small funded
  exact terminating_prefix source post template (.call (some (none,none)) (ofString "memcpy") arguments) continuation
    (CopyGeneral.cost src dst length+1) result execute run notTimeout

/-- Aligned whole-word zeroing derives its real funding and precise next
memory from the same enclosing execution, without a future return premise. -/
theorem zero_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst : BitVec 64) (length : Nat) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (code : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one))
    (small : length+32<2^64) (multiple : length%8=0) (aligned : dst.toNat%8=0)
    (mapped : ∀ offset,offset+8≤length → offset%8=0 → source.memaddrs (byteAddress dst offset))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) (ofString "memzero") arguments) continuation)=(result,post))
    (notTimeout : result≠some .timeOut) :
    Zero.price length+1≤source.clock ∧
      evaluateHOLFiniteState {source with memory:=Zero.finalMemory source.memory dst length,clock:=source.clock-(Zero.price length+1)} continuation=(result,post) := by
  let template := {source with memory:=Zero.finalMemory source.memory dst length}
  have execute (clock : Nat) (funded : Zero.price length+1≤clock) :
      evaluateHOLFiniteState {source with clock:=clock} (.call (some (none,none)) (ofString "memzero") arguments)=
        (none,{template with clock:=clock-(Zero.price length+1)}) := by
    have currentArgs : evalListHOLFinite {source with clock:=clock} (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length) := by
      rw [EvaluateClockSubCall.evalList_upd_clock]
      exact args
    exact Zero.call_execute {source with clock:=clock} arguments dst length currentArgs code small multiple aligned mapped funded
  exact terminating_prefix source post template (.call (some (none,none)) (ofString "memzero") arguments) continuation
    (Zero.price length+1) result execute run notTimeout

end InitECandidate.Solver.Input.BufferTrace

#print axioms InitECandidate.Solver.Input.BufferTrace.copy_prefix
#print axioms InitECandidate.Solver.Input.BufferTrace.zero_prefix
