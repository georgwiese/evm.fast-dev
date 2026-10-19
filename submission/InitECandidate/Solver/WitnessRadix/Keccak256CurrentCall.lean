import InitECandidate.Solver.WitnessRadix.Keccak256Normal
import InitECandidate.Solver.WitnessRadix.Keccak256Call
import InitECandidate.Solver.Input.ClockCostCurrentCall
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (destination : Option (Option MlS))
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (code : source.code.lookup (ofString "keccak256")=some (formals,body,.one))
    (data : EntryData source stp pointer scratch out length) (small : length+136<2^64) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "keccak256") arguments)).2.clock≤price length+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal,outLocal⟩ := environment source.code.lookup pointer out length code
  let entry := callEntryStateHOLFinite source callee
  have entryLocals : EntryLocals entry pointer out length := ⟨pointerLocal,lengthLocal,outLocal⟩
  have entryData := EntryData.of_control source entry stp pointer scratch out length rfl data
  exact Input.ClockCost.call_current source destination (ofString "keccak256") arguments _ body callee .one (price length)
    args called (body_cost entry stp pointer scratch out length entryLocals entryData small)

/-- The real ignored hash return derives its caller cost, caller locals,
control and protected-memory facts, with no supplied callee execution. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arguments : List (ExpHOL 64)) (stp pointer scratch out : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (code : source.code.lookup (ofString "keccak256")=some (formals,body,.one))
    (data : EntryData source stp pointer scratch out length) (small : length+136<2^64)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,target)) :
    target.locals=source.locals ∧ target.clock≤source.clock ∧ source.clock-(price length+1)≤target.clock ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧
      ∀ query,Protected stp scratch out query → target.memory query=source.memory query := by
  let padding := price length+1
  let padded := {source with clock := source.clock+padding}
  have paddedArgs : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) arguments=some (values pointer out length) :=
    (EvaluateClockSubCall.evalList_upd_clock source (source.clock+padding) arguments).trans args
  have paddedData := EntryData.of_control source padded stp pointer scratch out length rfl data
  obtain ⟨post,run,locals,upper,lower,control,memory⟩ := call_execute padded arguments stp pointer scratch out length paddedArgs code paddedData small
    (by change price length+1≤source.clock+padding; dsimp [padding]; omega)
  have lifted := panPropsEvaluateAddClockEq (.call (some (none,none)) (ofString "keccak256") arguments) source none target padding
    ⟨normal,by intro impossible; cases impossible⟩
  have postEq := congrArg Prod.snd (lifted.symm.trans run)
  change {target with clock := target.clock+padding}=post at postEq
  have clock := congrArg PanSemStateFiniteExact.clock postEq
  change target.clock+padding=post.clock at clock
  change post.clock≤source.clock+padding at upper
  change source.clock+padding-(price length+1)≤post.clock at lower
  rw [← postEq] at locals control memory
  exact ⟨locals,by omega,by dsimp [padding] at *; omega,control,memory⟩

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.call_cost
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.call_normal
