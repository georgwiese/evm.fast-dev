import InitECandidate.Solver.Input.ZeroUnmappedCall
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.ZeroUnmapped
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

/-- Exact first-loop observation; its four-word body fails on its first store. -/
theorem loop32_run {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2^64) (large : 32 ≤ length)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    evaluateHOLFiniteState source Zero.loop32 =
      if source.clock = 0 then (some .timeOut, emptyLocalsHOLFinite source) else (some .error, decClockHOLFinite source) := by
  classical
  have read := Zero.condition_read source 0 length 32 small (by omega) (by omega) indexLocal lengthLocal
  simp only [Nat.zero_add, if_pos large] at read
  have failed := block32_error (decClockHOLFinite source) dst domain below dstLocal indexLocal
  rw [Zero.loop32_shape, evaluateHOLFiniteState_while_total, read]
  simp only [show (1#64 : BitVec 64) ≠ 0 from by decide, ↓reduceIte]
  by_cases zero : source.clock = 0
  · simp [zero, show (1#64 : BitVec 64) ≠ 0 from by decide]
  · rw [if_neg zero, failed]
    simp [fixClockHOLFinite, decClockHOLFinite, zero, show (1#64 : BitVec 64) ≠ 0 from by decide]

/-- The complete current clear stops with timeout or error and spends at most
one source loop tick. Later word/byte/tail loops are never evaluated. -/
theorem body_stopped_price {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2^64) (large : 32 ≤ length) (aligned : dst.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    (evaluateHOLFiniteState source Zero.body).1 = some (if source.clock = 0 then .timeOut else .error) ∧
      source.clock - (evaluateHOLFiniteState source Zero.body).2.clock ≤ 1 := by
  let entered := bind source "i" 0#64
  have dstCell : entered.locals.lookup (ofString "dst") = some (.val (.word dst)) :=
    (bind_lookup_other source "i" "dst" 0#64 (by decide)).trans dstLocal
  have lengthCell : entered.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthLocal
  have test := Zero.alignment_read entered dst dstCell aligned
  simp only [eval] at test
  have first := loop32_run entered dst length small large domain below dstCell (bind_lookup_same _ _ _) lengthCell
  let tail := ProgHOL.seq (.ite Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip)
    (.seq Zero.loopBytes (.seq Zero.loopTail (.return (.const 0#64))))
  let output := evaluateHOLFiniteState entered tail
  have declared := ScalarScope.declare_execute source output.2 "i" (.const 0#64) 0#64 tail output.1 rfl rfl
  rw [Zero.body_shape, declared]
  change output.1 = _ ∧ source.clock - output.2.clock ≤ 1
  dsimp only [output, tail]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, test]
  simp only [show (1#64 : BitVec 64) ≠ 0 from by decide, ↓reduceIte, evaluateHOLFiniteState_seq_line780, first]
  by_cases zero : source.clock = 0
  · have enteredZero : entered.clock = 0 := zero
    simp only [enteredZero, if_pos, zero, Nat.zero_sub, Nat.zero_le, and_self]
  · have enteredNonzero : entered.clock ≠ 0 := zero
    simp only [if_neg enteredNonzero, if_neg zero]
    constructor
    · trivial
    · change source.clock - (source.clock - 1) ≤ 1
      omega

/-- Current ignored/tail/assignment calls add at most one call tick. -/
theorem call_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2^64) (large : 32 ≤ length) (aligned : dst.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : dst.toNat < InitE.sourceBase)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (Zero.values dst length)) :
    source.clock - (evaluateHOLFiniteState source
      (.call (LocalEffects.callInfo destination) (ofString "memzero") arguments)).2.clock ≤ 2 := by
  obtain ⟨callee, called, dstCell, lengthCell⟩ := Zero.environment source.code.lookup dst length
    (zero_installed source.code installed)
  exact ClockCost.call_current source destination (ofString "memzero") arguments (Zero.values dst length)
    Zero.body callee .one 1 args called
    (body_stopped_price (callEntryStateHOLFinite source callee) dst length small large aligned domain below dstCell lengthCell).2

end InitECandidate.Solver.Input.ZeroUnmapped

#print axioms InitECandidate.Solver.Input.ZeroUnmapped.loop32_run
#print axioms InitECandidate.Solver.Input.ZeroUnmapped.body_stopped_price
#print axioms InitECandidate.Solver.Input.ZeroUnmapped.call_price
