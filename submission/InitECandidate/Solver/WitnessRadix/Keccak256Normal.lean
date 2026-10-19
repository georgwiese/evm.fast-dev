import InitECandidate.Solver.WitnessRadix.Keccak256Execution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Current physical entry facts price every actual outcome, including a
timeout before the fully funded hash execution can complete. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (locals : EntryLocals source pointer out length)
    (data : EntryData source stp pointer scratch out length) (small : length+136<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock ≤ price length := by
  by_cases enough : price length ≤ source.clock
  · obtain ⟨post, run, upper, lower, control, memory⟩ := execute source stp pointer scratch out length locals data small enough
    rw [run]
    change source.clock-post.clock ≤ price length
    omega
  · omega

/-- An actual normal return determines the hash result, consumed clocks and
protected memory, without a future execution or funding premise. The control
projection retains the real FFI state except its appended event history. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (locals : EntryLocals source pointer out length)
    (data : EntryData source stp pointer scratch out length) (small : length+136<2^64)
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),target)) :
    returned=.val (.word 0#64) ∧ target.clock≤source.clock ∧ source.clock-price length≤target.clock ∧
      KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧
      ∀ query, Protected stp scratch out query → target.memory query=source.memory query := by
  let padded := {source with clock := source.clock+price length}
  have paddedLocals : EntryLocals padded pointer out length :=
    ⟨locals.pointerLocal,locals.lengthLocal,locals.outputLocal⟩
  have paddedData := EntryData.of_control source padded stp pointer scratch out length rfl data
  obtain ⟨post,run,upper,lower,control,memory⟩ := execute padded stp pointer scratch out length paddedLocals paddedData small
    (by change price length≤source.clock+price length; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) target (price length)
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans run)
  have postEq := congrArg Prod.snd (lifted.symm.trans run)
  change {target with clock := target.clock+price length}=post at postEq
  have clock := congrArg PanSemStateFiniteExact.clock postEq
  change target.clock+price length=post.clock at clock
  change post.clock≤source.clock+price length at upper
  change source.clock+price length-price length≤post.clock at lower
  rw [← postEq] at control memory
  exact ⟨by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,
    by omega,by omega,control,memory⟩

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.body_cost
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.body_normal
