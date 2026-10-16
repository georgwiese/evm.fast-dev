import InitECandidate.Solver.GuestWork.ChargeGasCost

namespace InitECandidate.Solver.GuestWork.GasAccounting
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate
open InitECandidate.Proofs.BackendStages
open InitECandidate.Solver.FlattenWeighted

/-- Concrete metadata/frame facts required by the actual charge_gas code.
These must eventually be supplied by the global guest-state invariant. -/
structure Ready {C F : Type} (source : StackSemStateFiniteExact 64 C F)
    (metadata offset heap globals frame gas used amount : BitVec 64)
    (returnLabel returnOffset : Nat) : Prop where
  metadataReg : source.regs.lookup 25 = some (.word metadata)
  heapReg : source.regs.lookup 26 = some (.word heap)
  amountReg : source.regs.lookup 10 = some (.word amount)
  returnReg : source.regs.lookup 1 = some (.loc returnLabel returnOffset)
  metadataDomain : source.mdomain (metadata + 18446744073709551592#64) = true
  metadataValue : source.memory (metadata + 18446744073709551592#64) = .word offset
  globalsEq : (offset <<< (1 : Nat)) + heap = globals
  globalDomain : source.mdomain (globals + 18446744073709551360#64) = true
  globalValue : source.memory (globals + 18446744073709551360#64) = .word frame
  gasDomain : source.mdomain (frame + 64#64) = true
  gasValue : source.memory (frame + 64#64) = .word gas
  usedDomain : source.mdomain (frame + 184#64) = true
  usedValue : source.memory (frame + 184#64) = .word used
  globalNotGas : globals + 18446744073709551360#64 ≠ frame + 64#64
  globalNotUsed : globals + 18446744073709551360#64 ≠ frame + 184#64

def gasLeft {C F : Type} (state : StackSemStateFiniteExact 64 C F) (frame : BitVec 64) : Nat :=
  match state.memory (frame + 64#64) with
  | .word gas => gas.toNat
  | _ => 0

def gasUsed {C F : Type} (state : StackSemStateFiniteExact 64 C F) (frame : BitVec 64) : Nat :=
  match state.memory (frame + 184#64) with
  | .word used => used.toNat
  | _ => 0

/-- Actual affordable charge execution conserves gas-left plus gas-used, with
exact natural-number consumption and no counter wrap. It also has Work 49 and
consumes exactly two source clock units. -/
theorem charge {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals frame gas used amount : BitVec 64) (returnLabel returnOffset : Nat)
    (ready : Ready source metadata offset heap globals frame gas used amount returnLabel returnOffset)
    (affordable : amount ≤ gas) (bounded : gas.toNat + used.toNat < 2 ^ 64)
    (enoughClock : 2 ≤ source.clock)
    (execution : evaluate (Named472.2, source) = (result, post)) :
    result = some (.result (.loc returnLabel returnOffset)) ∧
    gasLeft post frame + amount.toNat = gasLeft source frame ∧
    gasUsed post frame = gasUsed source frame + amount.toNat ∧
    gasLeft post frame + gasUsed post frame = gasLeft source frame + gasUsed source frame ∧
    source.clock = post.clock + 2 ∧ post.ffi = source.ffi ∧ Work Named472.2 source 49 := by
  obtain ⟨returned, nextGas, nextUsed, _, _, sameFfi, clock, _⟩ :=
    ChargeGasEntry.updates source post result metadata offset heap globals frame gas used amount
      returnLabel returnOffset ready.metadataReg ready.heapReg ready.amountReg ready.metadataDomain
      ready.metadataValue ready.globalsEq ready.gasValue affordable ready.returnReg ready.globalDomain
      ready.gasDomain ready.usedDomain ready.globalValue ready.usedValue ready.globalNotGas
      ready.globalNotUsed enoughClock execution
  have available : amount.toNat ≤ gas.toNat := affordable
  have subNat := BitVec.toNat_sub_of_le affordable
  have addNat : (amount + used).toNat = amount.toNat + used.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have consumed : gasLeft post frame + amount.toNat = gasLeft source frame := by
    simp only [gasLeft, nextGas, ready.gasValue, subNat]
    omega
  have spent : gasUsed post frame = gasUsed source frame + amount.toNat := by
    simp only [gasUsed, nextUsed, ready.usedValue, addNat]
    omega
  refine ⟨returned, consumed, spent, by omega, by omega, sameFfi, ?_⟩
  exact ChargeGasEntry.work source metadata offset heap globals frame gas amount
    ready.metadataReg ready.heapReg ready.amountReg ready.metadataDomain ready.metadataValue
    ready.globalsEq ready.globalDomain ready.globalValue ready.gasDomain ready.gasValue affordable

/-- Positive charges strictly decrease the actual frame's gas-left rank. This
alone does not assert that every guest iteration contains a positive charge. -/
theorem positive_charge_decreases {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (frame amount : BitVec 64)
    (consumed : gasLeft post frame + amount.toNat = gasLeft source frame)
    (positive : 0 < amount.toNat) : gasLeft post frame < gasLeft source frame := by omega

end InitECandidate.Solver.GuestWork.GasAccounting
#print axioms InitECandidate.Solver.GuestWork.GasAccounting.charge
#print axioms InitECandidate.Solver.GuestWork.GasAccounting.positive_charge_decreases
