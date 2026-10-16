import InitECandidate.Solver.GuestWork.ChargeGasTail

namespace InitECandidate.Solver.GuestWork.ChargeGasEntry
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open StackSemEvaluate StackSemStateOps StackSemExpressions StackSemIntegerInstructions
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted InitECandidate.Solver.FlattenBound
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem seqEvaluate {C F : Type} (p q : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) :
    evaluate (.seq p q, state) = match evaluate (p, state) with
      | (none, next) => evaluate (q, next)
      | (result, next) => (result, next) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (p, state) with ⟨result, next⟩
  cases result <;> rfl

/-- The actual charge_gas procedure on its affordable path. Metadata and frame
memory hypotheses are explicit; the global guest invariant must supply them. -/
theorem updates {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals frame gas used amount : BitVec 64) (returnLabel returnOffset : Nat)
    (hmetadata : source.regs.lookup 25 = some (.word metadata))
    (hheap : source.regs.lookup 26 = some (.word heap))
    (hamount : source.regs.lookup 10 = some (.word amount))
    (metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true)
    (metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset)
    (globalsEq : (offset <<< (1 : Nat)) + heap = globals)
    (gasValue : source.memory (frame + 64#64) = .word gas)
    (affordable : amount ≤ gas)
    (hreturn : source.regs.lookup 1 = some (.loc returnLabel returnOffset))
    (globalDomain : source.mdomain (globals + 18446744073709551360#64) = true)
    (gasDomain : source.mdomain (frame + 64#64) = true)
    (usedDomain : source.mdomain (frame + 184#64) = true)
    (globalValue : source.memory (globals + 18446744073709551360#64) = .word frame)
    (usedValue : source.memory (frame + 184#64) = .word used)
    (globalNotGas : globals + 18446744073709551360#64 ≠ frame + 64#64)
    (globalNotUsed : globals + 18446744073709551360#64 ≠ frame + 184#64)
    (enoughClock : 2 ≤ source.clock)
    (execution : evaluate (Named472.2, source) = (result, post)) :
    result = some (.result (.loc returnLabel returnOffset)) ∧
    post.memory (frame + 64#64) = .word (gas - amount) ∧
    post.memory (frame + 184#64) = .word (amount + used) ∧
    post.memory (globals + 18446744073709551360#64) = .word frame ∧
    post.mdomain = source.mdomain ∧ post.ffi = source.ffi ∧
    post.clock = source.clock - 2 ∧
    (∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 →
      post.memory address = source.memory address) := by
  have available : amount.toNat ≤ gas.toNat := affordable
  have noUnderflow : ¬ gas < amount := by
    change ¬ gas.toNat < amount.toNat
    omega
  have zero : source.clock ≠ 0 := by omega
  have one : source.clock - 1 ≠ 0 := by omega
  have usedNotGas : frame + 184#64 ≠ frame + 64#64 := by simp
  simp [Named472, NamedBody472_0, NamedBody472_1, NamedBody472_2, NamedBody472_3, NamedBody472_4, NamedBody472_5, NamedBody472_6, NamedBody472_7, NamedBody472_8, NamedBody472_9, NamedBody472_10, NamedBody472_11, NamedBody472_12, NamedBody472_13, NamedBody472_14, NamedBody472_15, NamedBody472_16, NamedBody472_17, NamedBody472_18, NamedBody472_19, NamedBody472_20, NamedBody472_21, NamedBody472_22, NamedBody472_23, NamedBody472_24, NamedBody472_25, NamedBody472_26, NamedBody472_27, NamedBody472_28, NamedBody472_29, NamedBody472_30, NamedBody472_31, NamedBody472_32, NamedBody472_33, NamedBody472_34, NamedBody472_35, NamedBody472_36, NamedBody472_37, NamedBody472_38, NamedBody472_39, NamedBody472_40, NamedBody472_41, NamedBody472_42, NamedBody472_43, NamedBody472_44, NamedBody472_45, NamedBody472_46, NamedBody472_47, NamedBody472_48, NamedBody472_49, NamedBody472_50, NamedBody472_51, NamedBody472_52, NamedBody472_53, NamedBody472_54, NamedBody472_55, NamedBody472_56, NamedBody472_57, NamedBody472_58, NamedBody472_59, NamedBody472_60, NamedBody472_61, NamedBody472_62, NamedBody472_63, NamedBody472_64, NamedBody472_65, NamedBody472_66, NamedBody472_67, NamedBody472_68,
    seqEvaluate, evaluate_skip, evaluate_tick, evaluate_inst, evaluate_ret, evaluate_ite,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm, Flapjack.Compiler.Encoders.Asm.HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL, wordShiftHOL, StackSemInst.instHOL, instInteger, assign, wordExp,
    wordOpHOL, wordOp, memLoad, memStore, setVar, decClock,
    hmetadata, hheap, hamount, hreturn, metadataDomain, metadataValue, globalsEq, gasValue, noUnderflow, globalDomain, gasDomain, usedDomain,
    globalValue, usedValue, globalNotGas, globalNotUsed, usedNotGas, zero, one,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at execution
  rcases execution with ⟨rfl, rfl⟩
  simp [usedNotGas, Ne.symm usedNotGas, globalNotGas, globalNotUsed, globalValue, Nat.sub_sub]
  intro address notGas notUsed
  simp [notGas, notUsed]

end InitECandidate.Solver.GuestWork.ChargeGasEntry
#print axioms InitECandidate.Solver.GuestWork.ChargeGasEntry.updates
