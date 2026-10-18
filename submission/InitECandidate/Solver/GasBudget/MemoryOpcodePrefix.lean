import InitECandidate.Solver.GasBudget.MemoryOpcodeProgram
import InitECandidate.Solver.GasBudget.MemoryChargeCallPrefix

namespace InitECandidate.Solver.GasBudget.MemoryOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_normal_prefix (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.body = (some (.returned value), post)) :
    ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ kind.names.length + 24 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready ChargeWithMemory.suffix (some (.returned value)) post := by
  rw [body_shape] at normal
  obtain ⟨popped, scopedPost, fits, clock, fields, poppedRun, scopeEq, budget, used, outside, depth⟩ :=
    StackPop.pops_normal kind.names source post frame _ (OriginalCodeEnvironment.stack_pop source.code installed) ev value normal
  have before : StackPop.PrefixEffect source popped frame kind.names.length :=
    ⟨fits, clock, by rw [clock]; exact fields, budget, used, outside⟩
  have original : Input.OriginalCode.Installed popped.code := by rw [before.code_eq]; exact installed
  have current : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
  have currentCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
  have safe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "charge_with_memory") kind.arguments) :=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨callPost, callRun, suffixRun, saved⟩ := safe.normal_continue popped scopedPost kind.suffix value poppedRun
  obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := ChargeWithMemory.call_normal_prefix popped callPost frame 3#64
    (WitnessRadix.QueryBranch.localVar "start") (.rstruct [.const kind.size, .const 0#64, .const 0#64, .const 0#64]) original (by decide) current currentCap callRun
  have amountBound : 3 ≤ amount.toNat := lower
  have rest := Input.ExecutionTail.next tail kind.suffix suffixRun
  exact ⟨kind.names.length + paid, amount, ready, by omega, amountBound, event.prepend before, .locals rest scopeEq⟩

theorem body_exception_prefix (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp gas used : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (spMapped : source.memaddrs (frame + 16#64)) (spCell : source.memory (frame + 16#64) = .word sp)
    (gasMapped : source.memaddrs (frame + 64#64)) (usedMapped : source.memaddrs (frame + 184#64))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source kind.body = (some (.exception identifier payload), post)) :
    (∃ paid, paid ≤ kind.names.length + 24 ∧ StackPop.PrefixEffect source post frame paid) ∨
    ∃ (paid : Nat) (amount : BitVec 64) (ready : PanSemStateFiniteExact 64 Guest.HostMemory), paid ≤ kind.names.length + 24 ∧ 3 ≤ amount.toNat ∧ ChargeEvent source ready frame paid amount.toNat ∧
      Input.ExecutionTail ready ChargeWithMemory.suffix (some (.exception identifier payload)) post := by
  rw [body_shape] at run
  rcases StackPop.pops_exception kind.names source post frame sp _ (OriginalCodeEnvironment.stack_pop source.code installed)
      ev spMapped spCell (shapes Input.OriginalExceptions.Kind.EvmErr) identifier payload run with failed | continued
  · obtain ⟨actualId, actualPayload, bound, effect, zero⟩ := failed
    exact Or.inl ⟨sp.toNat + 1, by omega, effect⟩
  · obtain ⟨popped, scopedPost, remaining, before, remainingCell, depth, poppedRun, scopeEq⟩ := continued
    have original : Input.OriginalCode.Installed popped.code := by rw [before.code_eq]; exact installed
    have current : popped.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
    have currentCap : regularBudget popped.memory frame ≤ 16777216 := by rw [before.budget]; exact cap
    rcases Input.sequence_exception popped scopedPost _ kind.suffix identifier payload poppedRun with escaped | afterCall
    · have currentShapes : Input.OriginalExceptions.Installed popped.eshapes := by rw [before.eshapes_eq]; exact shapes
      have currentSp : popped.memaddrs (frame + 16#64) := by rw [before.memaddrs_eq]; exact spMapped
      have currentGas : popped.memaddrs (frame + 64#64) := by rw [before.memaddrs_eq]; exact gasMapped
      have currentUsed : popped.memaddrs (frame + 184#64) := by rw [before.memaddrs_eq]; exact usedMapped
      have currentGasCell : popped.memory (frame + 64#64) = .word gas :=
        (before.outside _ (offsets_ne frame 64#64 16#64 (by decide))).trans gasCell
      have currentUsedCell : popped.memory (frame + 184#64) = .word used := before.used.trans usedCell
      rcases ChargeWithMemory.call_exception_prefix popped scopedPost frame 3#64 gas used
          (WitnessRadix.QueryBranch.localVar "start") (.rstruct [.const kind.size, .const 0#64, .const 0#64, .const 0#64]) original currentShapes
          (by decide) current currentSp currentGas currentUsed currentGasCell currentUsedCell currentCap identifier payload escaped with failed | charged
      · obtain ⟨paid, bound, effect⟩ := failed
        exact Or.inl ⟨kind.names.length + paid, by omega, (before.trans effect).of_emptyLocals scopeEq⟩
      · obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := charged
        have amountBound : 3 ≤ amount.toNat := lower
        exact Or.inr ⟨kind.names.length + paid, amount, ready, by omega, amountBound, event.prepend before, .locals tail scopeEq⟩
    · obtain ⟨callPost, callRun, suffixRun⟩ := afterCall
      obtain ⟨paid, amount, ready, bound, lower, event, tail⟩ := ChargeWithMemory.call_normal_prefix popped callPost frame 3#64
        (WitnessRadix.QueryBranch.localVar "start") (.rstruct [.const kind.size, .const 0#64, .const 0#64, .const 0#64]) original (by decide) current currentCap callRun
      have amountBound : 3 ≤ amount.toNat := lower
      have rest := Input.ExecutionTail.next tail kind.suffix suffixRun
      exact Or.inr ⟨kind.names.length + paid, amount, ready, by omega, amountBound, event.prepend before, .locals rest scopeEq⟩

end InitECandidate.Solver.GasBudget.MemoryOpcode

#print axioms InitECandidate.Solver.GasBudget.MemoryOpcode.body_normal_prefix
#print axioms InitECandidate.Solver.GasBudget.MemoryOpcode.body_exception_prefix
