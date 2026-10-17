import InitECandidate.Solver.WitnessRadix.Keccak256Execution
import InitECandidate.Solver.WitnessRadix.Keccak256Environment

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual fixed keccak256 caller/callee and every body path, from concrete
code/global/mapped-buffer facts. At most203+20*floor(length/136) call clocks. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (code : source.code.lookup (ofString "keccak256")=some (formals,body,.one))
    (data : EntryData source stp pointer scratch out length) (small : length+136<2^64) (enough : price length+1≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,output) ∧
      output.locals=source.locals ∧ output.clock≤source.clock ∧ source.clock-(price length+1)≤output.clock ∧
      KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      ∀ query,Protected stp scratch out query → output.memory query=source.memory query := by
  classical
  obtain ⟨callee,lookup,pointerLocal,lengthLocal,outLocal⟩ := environment source.code.lookup pointer out length code
  let entry := callEntryStateHOLFinite source callee
  have entryLocals : EntryLocals entry pointer out length := ⟨pointerLocal,lengthLocal,outLocal⟩
  have entryData := EntryData.of_control source entry stp pointer scratch out length rfl data
  obtain ⟨finished,run,upper,lower,control,memory⟩ := execute entry stp pointer scratch out length entryLocals entryData small
    (by change price length≤source.clock-1; omega)
  let output := {finished with locals := source.locals}
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak256") arguments
    (values pointer out length) body callee .one (.val (.word 0#64)) finished args lookup (by omega) run
    (by simp [shapeEqHOL,shapeOfHOLExact])
  refine ⟨output,callRun,rfl,?_,?_,control,memory⟩
  · change finished.clock≤source.clock
    change finished.clock≤source.clock-1 at upper
    omega
  · change source.clock-(price length+1)≤finished.clock
    change source.clock-1-price length≤finished.clock at lower
    omega

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.call_execute
