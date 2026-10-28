import InitECandidate.Solver.Input.Copy32Flow
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode

namespace InitECandidate.Solver.Input.Copy32Flow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A current bounded copy counter, retained only on real fallthrough. -/
structure Flow (code) (program : ProgHOL 64) (price : Nat) : Prop where
  cost : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code → CounterFlow.StrideInvariant 32 source →
    source.clock - (evaluateHOLFiniteState source program).2.clock ≤ price
  normal : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code → CounterFlow.StrideInvariant 32 source →
    evaluateHOLFiniteState source program = (none, post) → CounterFlow.StrideInvariant 32 post

theorem Flow.sequence (code) (first second : ProgHOL 64) (a b : Nat)
    (front : Flow code first a) (back : Flow code second b) : Flow code (.seq first second) (a+b) := by
  constructor
  · intro source installed valid
    exact ClockCost.sequence_reached_current source first second a b (front.cost source installed valid) (by
      intro middle run
      exact back.cost middle ((evaluation_fields source middle first none run).2.2.2.trans installed)
        (front.normal source middle installed valid run))
  · intro source post installed valid run
    obtain ⟨middle, firstRun, secondRun⟩ := Input.sequence_none source post first second run
    exact back.normal middle post ((evaluation_fields source middle first none firstRun).2.2.2.trans installed)
      (front.normal source middle installed valid firstRun) secondRun

theorem Flow.skip (code) : Flow code .skip 0 := by
  constructor
  · intro source installed valid; simp [evaluateHOLFiniteState_skip]
  · intro source post installed valid run
    rw [evaluateHOLFiniteState_skip] at run
    cases run
    exact valid

theorem Flow.conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (a b : Nat)
    (left : Flow code yes a) (right : Flow code no b) : Flow code (.ite test yes no) (max a b) := by
  constructor
  · intro source installed valid
    exact ClockCost.conditional_current source test yes no a b (left.cost source installed valid) (right.cost source installed valid)
  · intro source post installed valid run
    rw [evaluateHOLFiniteState_ite] at run
    generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) test = value at run
    cases value with
    | none => cases run
    | some value =>
      cases value with
      | rStruct fields => cases run
      | nStruct name fields => cases run
      | val value =>
        cases value with
        | word word =>
          change (if word=0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes)=(none,post) at run
          by_cases zero : word=0
          · rw [if_pos zero] at run; exact right.normal source post installed valid run
          · rw [if_neg zero] at run; exact left.normal source post installed valid run

theorem loop_flow (code) (test : ExpHOL 64) (body : ProgHOL 64) (stride : Nat)
    (positive : 0 < stride) (block : Block code body stride)
    (reads : CounterFlow.StrideReads test stride 32) : Flow code (.while test body) (32/stride) := by
  constructor
  · intro source installed valid
    have price := CounterFlow.stride_loop_cost code test body stride 32 0 positive (by decide)
      block.advance block.summary reads (ClockCost.of_quiet code body block.quiet) source installed valid
    have rank : CounterFlow.strideRank stride 32 source ≤ 32/stride :=
      Nat.div_le_div_right (Nat.sub_le _ _)
    simpa only [Nat.zero_add, Nat.one_mul] using Nat.le_trans price (by simpa only [Nat.zero_add, Nat.one_mul] using rank)
  · intro source post installed valid run
    exact CounterFlow.stride_loop_normal code test body stride 32 positive (by decide)
      block.advance block.summary reads source post installed valid run

theorem loops (code) : Flow code Copy32.loop32 1 ∧ Flow code Copy32.loopWord 4 ∧
    Flow code Copy32.loopBytes 4 ∧ Flow code Copy32.loopTail 32 := by
  rw [CopyWords.loop_shapes.1, CopyWords.loop_shapes.2, CopyBytes.loop_shapes.1, CopyBytes.loop_shapes.2]
  exact ⟨loop_flow code _ _ 32 (by decide) (word_stores code _ _ 32 (increment code 32)) (condition_reads 32 (by decide)),
    loop_flow code _ _ 8 (by decide) (word_stores code _ _ 8 (increment code 8)) (condition_reads 8 (by decide)),
    loop_flow code _ _ 8 (by decide) (byte_stores code _ _ 8 (increment code 8)) (condition_reads 8 (by decide)),
    loop_flow code _ _ 1 (by decide) (tail_block code) tail_reads⟩

/-- Every outcome of the unchanged 32-byte copy, even with unmapped
operands, is bounded by its real advancing counters. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : source.locals.lookup (ofString "n")=some (.val (.word 32#64))) :
    source.clock-(evaluateHOLFiniteState source Copy32.body).2.clock ≤ 41 := by
  let entry := bind source "i" 0#64
  have valid : CounterFlow.StrideInvariant 32 entry :=
    ⟨0#64, bind_lookup_same _ _ _, (bind_lookup_other source "i" "n" 0#64 (by decide)).trans length, by decide⟩
  obtain ⟨large, word, byte, tail⟩ := loops source.code
  have aligned := Flow.sequence source.code Copy32.loop32 Copy32.loopWord 1 4 large word
  have choice := Flow.conditional source.code Copy32.alignment _ .skip 5 0 aligned (Flow.skip source.code)
  rw [Copy32.body_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 41 rfl
  have front := ClockCost.sequence_reached_current entry (.ite Copy32.alignment (.seq Copy32.loop32 Copy32.loopWord) .skip)
    (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64)))) 5 36 (choice.cost entry rfl valid) (by
      intro middle run
      have middleValid := choice.normal entry middle rfl valid run
      have installed := (evaluation_fields entry middle _ none run).2.2.2
      exact ClockCost.sequence_reached_current middle Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64))) 4 32
        (byte.cost middle installed middleValid) (by
          intro current byteRun
          have currentValid := byte.normal middle current installed middleValid byteRun
          have currentCode := (evaluation_fields middle current _ none byteRun).2.2.2.trans installed
          exact ClockCost.sequence_current current Copy32.loopTail (.return (.const 0#64)) 32 0
            (tail.cost current currentCode currentValid) (ClockCost.returned current.code _)))
  exact front

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst src : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src 32))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock ≤ 42 := by
  obtain ⟨callee, called, dstCell, srcCell, length⟩ := CopyGeneral.environment source.code.lookup dst src 32
    (CopyGeneral.original_code source.code installed)
  exact ClockCost.call_current source (some none) (ofString "memcpy") arguments (CopyGeneral.values dst src 32)
    Copy32.body callee .one 41 args called (body_cost (callEntryStateHOLFinite source callee) length)

end InitECandidate.Solver.Input.Copy32Flow

#print axioms InitECandidate.Solver.Input.Copy32Flow.loops
#print axioms InitECandidate.Solver.Input.Copy32Flow.body_cost
#print axioms InitECandidate.Solver.Input.Copy32Flow.call_cost
