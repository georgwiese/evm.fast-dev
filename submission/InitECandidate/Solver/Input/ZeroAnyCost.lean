import InitECandidate.Solver.Input.ZeroAnyFlow
import InitECandidate.Solver.Input.ClockCostCurrentConditional
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentCall
import InitECandidate.Solver.WitnessRadix.ZeroEnvironment

namespace InitECandidate.Solver.Input.ZeroAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

def price (length : Nat) : Nat:=length/32+length/8+length/8+length

theorem Loop.uniform_cost (loop : Loop) (length : Nat) (small : length+32<2^64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source loop.program).2.clock≤length/loop.stride:=
  (loop.cost length small source valid).trans (Nat.div_le_div_right (Nat.sub_le length _))

private theorem conditional_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (test : ExpHOL 64) (yes no : ProgHOL 64) (length : Nat)
    (left : evaluateHOLFiniteState source yes=(none,post)→StrideInvariant length post)
    (right : evaluateHOLFiniteState source no=(none,post)→StrideInvariant length post)
    (normal : evaluateHOLFiniteState source (.ite test yes no)=(none,post)) : StrideInvariant length post:=by
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) test=value at normal
  cases value with
  | none=>simp at normal
  | some value=>
    cases value with
    | rStruct fields=>simp at normal
    | nStruct name fields=>simp at normal
    | val payload=>
      cases payload with
      | word word=>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero] at normal; exact right normal
        · rw [if_neg zero] at normal; exact left normal

theorem aligned_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source (.seq Zero.loop32 Zero.loopWord)).2.clock≤length/32+length/8:=by
  exact ClockCost.sequence_reached_current source Zero.loop32 Zero.loopWord (length/32) (length/8)
    (Loop.block32.uniform_cost length small source valid) (fun middle normal=>Loop.word.uniform_cost length small middle (Loop.block32.normal length small source middle valid normal))

theorem aligned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source (.seq Zero.loop32 Zero.loopWord)=(none,post)) : StrideInvariant length post:=by
  obtain ⟨middle,front,back⟩:=sequence_none source post _ _ normal
  exact Loop.word.normal length small middle post (Loop.block32.normal length small source middle valid front) back

theorem after_alignment_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source (.seq Zero.loopBytes (.seq Zero.loopTail (.return (.const 0#64))))).2.clock≤length/8+length:=by
  apply ClockCost.sequence_reached_current source Zero.loopBytes _ (length/8) length
    (Loop.bytes.uniform_cost length small source valid)
  intro middle normal
  have next:=Loop.bytes.normal length small source middle valid normal
  have tail:=Loop.tail.uniform_cost length small middle next
  have result:=ClockCost.sequence_current middle Zero.loopTail (.return (.const 0#64)) length 0 (by simpa only [Loop.program,Loop.stride,Nat.div_one] using tail)
    (ClockCost.returned middle.code _)
  simpa only [Nat.add_zero] using result

/-- All original memzero outcomes, with no pointer, alignment, mapping,
successful store, allocator-room or future-execution premise. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat)
    (small : length+32<2^64)
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source Zero.body).2.clock≤price length:=by
  rw [Zero.body_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ (price length) rfl
  let entry:=bind source "i" 0#64
  have initial : StrideInvariant length entry:=⟨0#64,bind_lookup_same _ _ _,
    (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell,by simp⟩
  have front:=ClockCost.conditional_current entry Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip (length/32+length/8) 0
    (aligned_cost entry length small initial) (ClockCost.skip entry.code entry rfl)
  simp only [Nat.max_zero] at front
  have combined:=ClockCost.sequence_reached_current entry (.ite Zero.alignment (.seq Zero.loop32 Zero.loopWord) .skip)
    (.seq Zero.loopBytes (.seq Zero.loopTail (.return (.const 0#64)))) (length/32+length/8) (length/8+length) front (by
      intro middle normal
      have valid : StrideInvariant length middle:=conditional_normal entry middle _ _ _ length
        (aligned_normal entry middle length small initial) (by intro skipped; rw [evaluateHOLFiniteState_skip] at skipped; have same:entry=middle:=congrArg Prod.snd skipped; rewrite [←same]; exact initial) normal
      exact after_alignment_cost middle length small valid)
  simpa only [price,Nat.add_assoc] using combined

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst : BitVec 64) (length : Nat) (small : length+32<2^64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Zero.values dst length))
    (code : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)).2.clock≤price length+1:=by
  obtain ⟨callee,called,dstCell,lengthCell⟩:=Zero.environment source.code.lookup dst length code
  exact ClockCost.call_current source (some none) (ofString "memzero") arguments (Zero.values dst length) Zero.body callee .one (price length)
    args called (body_cost (callEntryStateHOLFinite source callee) length small lengthCell)

end InitECandidate.Solver.Input.ZeroAny

#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.uniform_cost
#print axioms InitECandidate.Solver.Input.ZeroAny.aligned_cost
#print axioms InitECandidate.Solver.Input.ZeroAny.aligned_normal
#print axioms InitECandidate.Solver.Input.ZeroAny.after_alignment_cost
#print axioms InitECandidate.Solver.Input.ZeroAny.body_cost
#print axioms InitECandidate.Solver.Input.ZeroAny.call_cost
