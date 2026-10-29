import InitECandidate.Solver.Input.CounterStrideCost
import InitECandidate.Solver.Input.ZeroByteFlow
import InitECandidate.Solver.WitnessRadix.ZeroConditions
import InitECandidate.Solver.WitnessRadix.ZeroLoopTail

namespace InitECandidate.Solver.Input.ZeroAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

inductive Loop where | block32 | word | bytes | tail

def Loop.stride : Loop→Nat
  | .block32=>32
  | .word | .bytes=>8
  | .tail=>1
def Loop.block : Loop→ProgHOL 64
  | .block32=>Zero.block32
  | .word=>Zero.blockWord
  | .bytes=>Zero.byteBody
  | .tail=>Zero.tailBody
def Loop.test : Loop→ExpHOL 64
  | .block32=>Zero.condition 32#64
  | .word | .bytes=>Zero.condition 8#64
  | .tail=>.cmp .lower (localVar "i") (localVar "n")
def Loop.program : Loop→ProgHOL 64
  | .block32=>Zero.loop32
  | .word=>Zero.loopWord
  | .bytes=>Zero.loopBytes
  | .tail=>Zero.loopTail

theorem Loop.shape (loop : Loop) : loop.program=.while loop.test loop.block:=by
  cases loop with
  | block32=>exact Zero.loop32_shape
  | word=>exact Zero.loopWord_shape
  | bytes=>exact Zero.other_loop_shapes.1
  | tail=>exact Zero.other_loop_shapes.2

theorem Loop.advance (loop : Loop) : Advances (ofString "i") loop.stride loop.block:=by
  cases loop with
  | block32=>
    simp only [Loop.block,Loop.stride,Zero.block32]
    repeat apply CounterFlow.sequence (ofString "i") _ _ 0 32 (CounterFlow.preserved (ofString "i") _ (.store _ _))
    exact CounterFlow.increment_by (ofString "i") 32
  | word=>
    exact CounterFlow.sequence (ofString "i") _ _ 0 8 (CounterFlow.preserved (ofString "i") _ (.store _ _)) (CounterFlow.increment_by (ofString "i") 8)
  | bytes=>exact ZeroByteFlow.byte_advance
  | tail=>exact ZeroByteFlow.tail_advance

theorem Loop.summary (loop : Loop) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    LocalSummary (ofString "n") loop.block source:=by
  cases loop with
  | block32=>
    simp only [Loop.block,Zero.block32]
    repeat (apply local_summary_sequence (ofString "n") _ _ (LocalPrefix.store _ _).summary_full; intro current)
    exact (LocalPrefix.assign _ _ (by decide)).summary_full _
  | word=>
    exact local_summary_sequence (ofString "n") _ _ (LocalPrefix.store _ _).summary_full
      (LocalPrefix.assign _ _ (by decide)).summary_full source
  | bytes=>exact ZeroByteFlow.byte_summary _ (by decide) source
  | tail=>exact ZeroByteFlow.tail_summary _ (by decide) source

theorem Loop.quiet (loop : Loop) (code) : QuietClock.Preserves code loop.block:=by
  cases loop with
  | block32=>
    simp only [Loop.block,Zero.block32]
    repeat apply QuietClock.sequence code _ _ (QuietClock.store code _ _)
    exact QuietClock.assign code _ _
  | word=>exact QuietClock.sequence code _ _ (QuietClock.store code _ _) (QuietClock.assign code _ _)
  | bytes=>exact ZeroByteFlow.byte_quiet code
  | tail=>exact ZeroByteFlow.tail_quiet code

theorem Loop.reads (loop : Loop) (length : Nat) (small : length+32<2^64) :
    StrideReads loop.test loop.stride length:=by
  intro source word indexCell lengthCell bounded
  have indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 word.toNat))):=by
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using indexCell
  cases loop with
  | block32=>exact Zero.condition_read source word.toNat length 32 small bounded (by decide) indexLocal lengthCell
  | word=>exact Zero.condition_read source word.toNat length 8 small bounded (by decide) indexLocal lengthCell
  | bytes=>exact Zero.condition_read source word.toNat length 8 small bounded (by decide) indexLocal lengthCell
  | tail=>
    have read:=Zero.tail_condition source word.toNat length (by omega) bounded indexLocal lengthCell
    change evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      (.cmp .lower (localVar "i") (localVar "n"))=some (.val (.word (if word.toNat+1≤length then 1#64 else 0#64)))
    by_cases active : word.toNat<length
    · simpa only [if_pos active,if_pos (show word.toNat+1≤length by omega)] using read
    · simpa only [if_neg active,if_neg (show ¬word.toNat+1≤length by omega)] using read

/-- Every original zeroing loop has finite counter progress even when
stores fail or operands point outside mapped memory. -/
theorem Loop.cost (loop : Loop) (length : Nat) (small : length+32<2^64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source loop.program).2.clock≤strideRank loop.stride length source:=by
  rw [loop.shape]
  have price:=stride_loop_cost source.code loop.test loop.block loop.stride length 0 (by cases loop <;> decide)
    (by omega) loop.advance loop.summary (loop.reads length small) (ClockCost.of_quiet _ _ (loop.quiet source.code)) source rfl valid
  simpa only [Nat.zero_add,Nat.one_mul] using price

theorem Loop.normal (loop : Loop) (length : Nat) (small : length+32<2^64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : StrideInvariant length source)
    (run : evaluateHOLFiniteState source loop.program=(none,target)) : StrideInvariant length target:=by
  rw [loop.shape] at run
  exact stride_loop_normal source.code loop.test loop.block loop.stride length (by cases loop <;> decide)
    (by omega) loop.advance loop.summary (loop.reads length small) source target rfl valid run

end InitECandidate.Solver.Input.ZeroAny

#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.advance
#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.summary
#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.quiet
#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.reads
#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.cost
#print axioms InitECandidate.Solver.Input.ZeroAny.Loop.normal
