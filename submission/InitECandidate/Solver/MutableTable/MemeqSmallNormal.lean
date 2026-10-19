import InitECandidate.Solver.MutableTable.MemeqSmallExecution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.MutableTable.MemeqSmall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem price_le_length (length : Nat) : MemeqByteRuntime.price length ≤ length := by
  have parts := Nat.mod_add_div length 8
  unfold MemeqByteRuntime.price
  omega

theorem price_le_fourteen (length : Nat) (small : length ≤ 64) : MemeqByteRuntime.price length ≤ 14 := by
  have parts := Nat.mod_add_div length 8
  have remainder := Nat.mod_lt length (by decide : 0 < 8)
  unfold MemeqByteRuntime.price
  omega

/-- Current mapped comparison regions suffice for an all-outcome source
clock bound. Below the allowance the evaluator clock itself supplies it;
otherwise the actual original executor finishes within that allowance. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset))) :
    source.clock - (evaluateHOLFiniteState source Memeq32.body).2.clock ≤ MemeqByteRuntime.price length := by
  by_cases enough : MemeqByteRuntime.price length ≤ source.clock
  · obtain ⟨spent, answer, post, bound, binary, run, fields⟩ :=
      execute source a b length aLocal bLocal lengthLocal small aFits bFits leftMapped rightMapped enough
    have clock := congrArg PanSemStateFiniteExact.clock fields
    change post.clock = source.clock - spent at clock
    rw [run]
    change source.clock - post.clock ≤ _
    omega
  · omega

/-- A real normal return supplies the original binary answer, funding and
readonly frame. No speculative normal helper execution is a premise. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b") = some (.val (.word b)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Memeq32.body = (some (.returned returned), target)) :
    ∃ spent answer, spent ≤ MemeqByteRuntime.price length ∧ spent ≤ source.clock ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      returned = .val (.word answer) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - spent} := by
  let extra := MemeqByteRuntime.price length
  let padded := {source with clock := source.clock + extra}
  obtain ⟨spent, answer, post, bounded, binary, actual, modelFrame⟩ :=
    execute padded a b length aLocal bLocal lengthLocal small aFits bFits leftMapped rightMapped
      (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq Memeq32.body source (some (.returned returned)) target extra
    ⟨normal, by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have postEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + extra} = post at postEq
  have frame : emptyLocalsHOLFinite {target with clock := target.clock + extra} =
      emptyLocalsHOLFinite {source with clock := source.clock + extra - spent} := by
    rw [postEq]
    exact modelFrame
  have stripped := InitECandidate.Solver.strip_clock_padding source target source spent extra
    (by change spent ≤ extra at bounded; omega) frame
  refine ⟨spent, answer, bounded, stripped.1, binary, ?_, stripped.2⟩
  simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq

end InitECandidate.Solver.MutableTable.MemeqSmall

#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.price_le_length
#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.price_le_fourteen
#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.body_cost
#print axioms InitECandidate.Solver.MutableTable.MemeqSmall.body_normal
