import InitECandidate.Solver.FlattenWeighted.BasicTimeout
import InitECandidate.Solver.FlattenWeighted.Work
import InitECandidate.Proofs.BackendStages.Named472

namespace InitECandidate.Solver.GuestWork.ChargeGasTail
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual charge_gas suffix reached after its out-of-gas guard. -/
def body : HolProg 64 := NamedBody472_59

theorem body_basic : basic body = true := by decide
theorem body_nodes : nodes body = 37 := by decide
theorem body_ticks : ticks body = 2 := by decide

theorem body_work {C F : Type} (source : StackSemStateFiniteExact 64 C F) :
    Work body source 39 := by
  simpa only [body_ticks, body_nodes] using (Work.basic (source := source) body_basic)

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

/-- The fixed stores update gas-left and regular-gas-used, preserving the frame
pointer and every other memory address. The disjointness hypotheses expose the
caller/global-memory invariant that still must be established for the guest. -/
theorem updates {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (globals frame gas used amount : BitVec 64) (returnLabel returnOffset : Nat)
    (hglobals : source.regs.lookup 11 = some (.word globals))
    (hframe : source.regs.lookup 13 = some (.word frame))
    (hgas : source.regs.lookup 5 = some (.word gas))
    (hamount : source.regs.lookup 12 = some (.word amount))
    (hreturn : source.regs.lookup 1 = some (.loc returnLabel returnOffset))
    (globalDomain : source.mdomain (globals + 18446744073709551360#64) = true)
    (gasDomain : source.mdomain (frame + 64#64) = true)
    (usedDomain : source.mdomain (frame + 184#64) = true)
    (globalValue : source.memory (globals + 18446744073709551360#64) = .word frame)
    (usedValue : source.memory (frame + 184#64) = .word used)
    (globalNotGas : globals + 18446744073709551360#64 ≠ frame + 64#64)
    (globalNotUsed : globals + 18446744073709551360#64 ≠ frame + 184#64)
    (enoughClock : 2 ≤ source.clock)
    (execution : evaluate (body, source) = (result, post)) :
    result = some (.result (.loc returnLabel returnOffset)) ∧
    post.memory (frame + 64#64) = .word (gas - amount) ∧
    post.memory (frame + 184#64) = .word (amount + used) ∧
    post.memory (globals + 18446744073709551360#64) = .word frame ∧
    post.mdomain = source.mdomain ∧ post.ffi = source.ffi ∧
    post.clock = source.clock - 2 ∧
    (∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 →
      post.memory address = source.memory address) := by
  have zero : source.clock ≠ 0 := by omega
  have one : source.clock - 1 ≠ 0 := by omega
  have usedNotGas : frame + 184#64 ≠ frame + 64#64 := by simp
  simp [body, NamedBody472_23, NamedBody472_24, NamedBody472_25, NamedBody472_26, NamedBody472_27, NamedBody472_28, NamedBody472_29, NamedBody472_30, NamedBody472_31, NamedBody472_32, NamedBody472_33, NamedBody472_34, NamedBody472_35, NamedBody472_36, NamedBody472_37, NamedBody472_38, NamedBody472_39, NamedBody472_40, NamedBody472_41, NamedBody472_42, NamedBody472_43, NamedBody472_44, NamedBody472_45, NamedBody472_46, NamedBody472_47, NamedBody472_48, NamedBody472_49, NamedBody472_50, NamedBody472_51, NamedBody472_52, NamedBody472_53, NamedBody472_54, NamedBody472_55, NamedBody472_56, NamedBody472_57, NamedBody472_58, NamedBody472_59,
    seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret,
    StackSemStateOps.getVar, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
    hglobals, hframe, hgas, hamount, hreturn, globalDomain, gasDomain, usedDomain,
    globalValue, usedValue, globalNotGas, globalNotUsed, usedNotGas, zero, one,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
  rcases execution with ⟨rfl, rfl⟩
  simp [usedNotGas, Ne.symm usedNotGas, globalNotGas, globalNotUsed, globalValue, Nat.sub_sub]
  intro address notGas notUsed
  simp [notGas, notUsed]

end InitECandidate.Solver.GuestWork.ChargeGasTail
#print axioms InitECandidate.Solver.GuestWork.ChargeGasTail.body_basic
#print axioms InitECandidate.Solver.GuestWork.ChargeGasTail.body_nodes
#print axioms InitECandidate.Solver.GuestWork.ChargeGasTail.body_ticks
#print axioms InitECandidate.Solver.GuestWork.ChargeGasTail.body_work
#print axioms InitECandidate.Solver.GuestWork.ChargeGasTail.updates
