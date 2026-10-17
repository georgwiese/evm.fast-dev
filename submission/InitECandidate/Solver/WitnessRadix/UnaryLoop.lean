import InitECandidate.Solver.WitnessRadix.UnaryCount
import InitECandidate.Solver.WitnessRadix.TerminalReads

namespace InitECandidate.Solver.WitnessRadix.UnaryProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem not_terminal {F : Type} (source : PanSemStateFiniteExact 64 F) (count position : Nat)
    (small : count < 2 ^ 64) (many : 1 < count) (inside : position < 256)
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position)))) :
    eval source TerminalProgram.terminalTest = some (.val (.word 0#64)) := by
  have countNe : BitVec.ofNat 64 count ≠ 1#64 := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
    change count = 1 at numeric
    omega
  have bitNe : BitVec.ofNat 64 position ≠ 256#64 := by
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show position < 2 ^ 64 by omega)] at numeric
    change position = 256 at numeric
    omega
  simpa only [countNe, bitNe, or_self, ↓reduceIte] using
    TerminalProgram.terminal_test source _ _ countLocal bitLocal

theorem main_body_unary {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start keys : BitVec 64) (keyFor : BitVec 64 → ByteKeys.Key)
    (input : List (BitVec 64)) (position : Nat)
    (inside : position < 256) (small : input.length < 2 ^ 64) (many : 1 < input.length)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 input.length))))
    (rows : BuildCopy.Rows source.memory source.memaddrs src start 0 input)
    (views : ∀ ordinal ∈ input, MemoryBytes.ByteView source (keys + ordinal * 32#64) (keyFor ordinal))
    (unary : CountProgram.zeroCount keyFor position input = 0 ∨
      CountProgram.zeroCount keyFor position input = input.length)
    (enough : input.length ≤ source.clock) :
    evaluateHOLFiniteState source BuildEntry.mainBody =
      (some .continue, bind { source with clock := source.clock - input.length }
        "bit" (BitVec.ofNat 64 position + 1#64)) := by
  classical
  have test := not_terminal source input.length position small many inside countLocal bitLocal
  have skipped : evaluateHOLFiniteState source (.ite TerminalProgram.terminalTest TerminalProgram.terminalCode .skip) =
      (none, source) := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simp
  rw [TerminalProgram.main_body_shape, StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
  exact count_scope_unary source src start keys keyFor input position inside small srcLocal startLocal keysLocal
    bitLocal countLocal rows views unary enough

/-- Exact outer iteration for a shared bit: count the interval, advance bit,
restore temporary counters and resume, at a cost of input.length + 1 clocks. -/
theorem main_loop_unary {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start keys : BitVec 64) (keyFor : BitVec 64 → ByteKeys.Key)
    (input : List (BitVec 64)) (position : Nat)
    (inside : position < 256) (small : input.length < 2 ^ 64) (many : 1 < input.length)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 input.length))))
    (rows : BuildCopy.Rows source.memory source.memaddrs src start 0 input)
    (views : ∀ ordinal ∈ input, MemoryBytes.ByteView source (keys + ordinal * 32#64) (keyFor ordinal))
    (unary : CountProgram.zeroCount keyFor position input = 0 ∨
      CountProgram.zeroCount keyFor position input = input.length)
    (enough : input.length + 1 ≤ source.clock) :
    evaluateHOLFiniteState source BuildEntry.mainLoop =
      evaluateHOLFiniteState (bind { source with clock := source.clock - (input.length + 1) }
        "bit" (BitVec.ofNat 64 position + 1#64)) BuildEntry.mainLoop := by
  classical
  let next := bind { source with clock := source.clock - (input.length + 1) }
    "bit" (BitVec.ofNat 64 position + 1#64)
  have views' : ∀ ordinal ∈ input, MemoryBytes.ByteView (decClockHOLFinite source)
      (keys + ordinal * 32#64) (keyFor ordinal) := by
    intro ordinal member
    exact MemoryBytes.byteView_of_fields source (decClockHOLFinite source) rfl rfl rfl _ _ (views ordinal member)
  have clockSub : source.clock - 1 - input.length = source.clock - (input.length + 1) := by omega
  have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) BuildEntry.mainBody = (some .continue, next) := by
    have run := main_body_unary (decClockHOLFinite source) src start keys keyFor input position inside small many
      srcLocal startLocal keysLocal bitLocal countLocal rows views' unary (by change input.length ≤ source.clock - 1; omega)
    simpa only [decClockHOLFinite, clockSub] using run
  have positive : source.clock ≠ 0 := by omega
  rw [TerminalProgram.main_loop_shape, evaluateHOLFiniteState_while_total]
  simp only [evalHOLFinite, evalHOLExact]
  rw [if_pos (by decide)]
  simp only [if_neg positive, bodyRun]
  rw [StateSteps.fixed_clock (decClockHOLFinite source) next _ (by
    change source.clock - (input.length + 1) ≤ source.clock - 1
    omega)]

end InitECandidate.Solver.WitnessRadix.UnaryProgram

#print axioms InitECandidate.Solver.WitnessRadix.UnaryProgram.main_loop_unary
