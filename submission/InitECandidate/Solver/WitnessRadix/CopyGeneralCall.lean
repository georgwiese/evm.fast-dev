import InitECandidate.Solver.WitnessRadix.CopyGeneralMemoryResult
import InitECandidate.Solver.WitnessRadix.CopyGeneralEnvironment
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString CopyContext

def callState {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) : PanSemStateFiniteExact 64 F :=
  { source with memory := resultMemory source.memory source.be src dst length, clock := source.clock - (cost src dst length + 1) }

/-- The actual memcpy caller/callee ABI and all function paths, with exact
memory, caller restoration and at most length+1 source clocks. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values dst src length))
    (code : source.code.lookup (ofString "memcpy") = some (formals, Copy32.body, .one))
    (mapped : Mapped source src dst length) (small : length + 32 < 2 ^ 64) (enough : cost src dst length + 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memcpy") arguments) = (none, callState source src dst length) := by
  classical
  obtain ⟨callee, lookup, dstLocal, srcLocal, lengthLocal⟩ := environment source.code.lookup dst src length code
  let entry := callEntryStateHOLFinite source callee
  have entryArgs : Args entry src dst length := ⟨srcLocal, dstLocal, lengthLocal⟩
  have entryMapped := Mapped.of_domain source entry src dst length rfl mapped
  obtain ⟨target, run, frame⟩ := execute entry src dst length entryArgs entryMapped small (by change cost src dst length ≤ source.clock - 1; omega)
  rw [core_memory] at frame
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "memcpy")
    arguments (values dst src length) Copy32.body callee .one (.val (.word 0#64)) target args lookup (by omega) run
    (by simp [shapeEqHOL, shapeOfHOLExact])
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with locals := source.locals }) frame
  have clockEq : source.clock - 1 - cost src dst length = source.clock - (cost src dst length + 1) := by omega
  simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, QueryBranch.bind, setVarHOLFinite, callState, clockEq] using callRun.trans
    (congrArg (fun state : PanSemStateFiniteExact 64 F => (none, state)) restored)

theorem call_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst query : BitVec 64) (length : Nat)
    (away : Away dst query length) : (callState source src dst length).memory query = source.memory query :=
  resultMemory_away source.memory source.be src dst query length away

theorem call_control {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    control (callState source src dst length) = control source := rfl

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_execute
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_memory_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_control
