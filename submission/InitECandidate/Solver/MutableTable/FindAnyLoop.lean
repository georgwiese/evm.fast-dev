import InitECandidate.Solver.MutableTable.FindAnyStep
import InitECandidate.Solver.MutableTable.FindGeneralChain
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A genuine finite occupied-slot chain bounds the actual loop on every
outcome. Comparisons use arbitrary memory; unreadable query bytes can exit
early and need no mapping, alignment or logical-key premise. -/
theorem any_chain_cost (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (index : BitVec 64) (length : Nat) (chain : GeneralChain snapshot p .word index length)
    (keyLength : p.keyLength=32#64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (locals : Locals source p index)
    (same : Input.LocalEffects.erase source=Input.LocalEffects.erase snapshot)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤6*length := by
  induction chain generalizing source with
  | empty index inside loaded =>
    have memory:=Input.LocalEffects.memory_of_erase snapshot source same
    have domain:=congrArg PanSemStateFiniteExact.memaddrs same
    have endian:=congrArg PanSemStateFiniteExact.be same
    have actual : usedByte source p index=some 0 := by
      rw [usedByte_of_fields source snapshot p index memory domain endian]
      exact loaded
    have test : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word 0#64)) := by
      simpa [QueryBranch.eval,evalHOLFinite] using condition_read source p index locals 0 actual
    rw [loop,evaluateHOLFiniteState_while_total,test]
    simp
  | occupied index byte length inside nonzero loaded fits mapped tail ih =>
    have memory:=Input.LocalEffects.memory_of_erase snapshot source same
    have domain:=congrArg PanSemStateFiniteExact.memaddrs same
    have endian:=congrArg PanSemStateFiniteExact.be same
    have actual : usedByte source p index=some byte := by
      rw [usedByte_of_fields source snapshot p index memory domain endian]
      exact loaded
    have byteNonzero : byte.toNat≠0 := by
      intro zero
      exact nonzero (UInt8.toNat.inj zero)
    have test : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word 1#64)) := by
      simpa only [QueryBranch.eval,evalHOLFinite,if_neg byteNonzero] using condition_read source p index locals byte actual
    rw [loop,evaluateHOLFiniteState_while_total,test]
    simp only [if_pos (by decide : (1#64 : BitVec 64)≠0#64)]
    by_cases zero : source.clock=0
    · rw [if_pos zero]
      simp [zero]
    · rw [if_neg zero]
      have entryLocals : Locals (decClockHOLFinite source) p index :=
        ⟨locals.cap,locals.klen,locals.stride,locals.keys,locals.used,locals.key,locals.index⟩
      have cost:=any_step_cost (decClockHOLFinite source) p index entryLocals keyLength code
      have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) loopBody
      have pure:=any_step_readonly source.code code (decClockHOLFinite source) rfl
      generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) loopBody=output at cost forward pure ⊢
      obtain ⟨result,target⟩ := output
      have fixed:=StateSteps.fixed_clock (decClockHOLFinite source) target result forward
      simp only [fixed]
      change source.clock-1-target.clock≤5 at cost
      change target.clock≤source.clock-1 at forward
      have stopped : source.clock-target.clock≤6*(length+1) := by omega
      cases result with
      | none =>
        have nextLocals:=any_step_normal (decClockHOLFinite source) target p index entryLocals keyLength code computed
        have nextFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase snapshot := pure.trans same
        have targetCode:=Input.LocalEffects.code_of_erase source target pure
        have nextInstalled : target.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one) := by rw [targetCode]; exact code
        have back:=ih target nextLocals nextFrame nextInstalled
        have backForward:=evaluateHOLFiniteState_clock_le target loop
        change source.clock-(evaluateHOLFiniteState target loop).2.clock≤6*(length+1)
        omega
      | some result =>
        cases result with
        | «continue» =>
          exact False.elim ((any_step_no_control (decClockHOLFinite source)).2 (congrArg Prod.fst computed))
        | _ => exact stopped

/-- The actual absent-cap return after the loop costs no additional ticks. -/
theorem any_chain_suffix_cost (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (index : BitVec 64) (length : Nat) (chain : GeneralChain snapshot p .word index length)
    (keyLength : p.keyLength=32#64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (locals : Locals source p index)
    (same : Input.LocalEffects.erase source=Input.LocalEffects.erase snapshot)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)) :
    source.clock-(evaluateHOLFiniteState source afterIndex).2.clock≤6*length := by
  have cost:=Input.ClockCost.sequence_reached_current source loop (.return (.var .local (ofString "cap"))) (6*length) 0
    (any_chain_cost snapshot p index length chain keyLength source locals same code)
    (by intro middle normal; exact Input.ClockCost.returned middle.code _ middle rfl)
  simpa only [afterIndex,Nat.add_zero,QueryBranch.localVar] using cost

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_chain_cost
#print axioms InitECandidate.Solver.MutableTable.Find.any_chain_suffix_cost
