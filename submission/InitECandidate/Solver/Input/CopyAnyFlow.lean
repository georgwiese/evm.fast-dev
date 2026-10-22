import InitECandidate.Solver.Input.Copy32Flow
import InitECandidate.Solver.Input.ZeroAnyFlow

namespace InitECandidate.Solver.Input.CopyAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch CounterFlow

inductive Loop where | block32 | word | bytes | tail

def Loop.zeroLoop : Loop→ZeroAny.Loop
  | .block32=>.block32 | .word=>.word | .bytes=>.bytes | .tail=>.tail
def Loop.stride (loop : Loop) := loop.zeroLoop.stride
def Loop.block : Loop→ProgHOL 64
  | .block32=>CopyWords.stores [0,8,16,24] (CopyBytes.increment 32#64)
  | .word=>CopyWords.stores [0] (CopyBytes.increment 8#64)
  | .bytes=>CopyBytes.byteBody | .tail=>CopyBytes.tailBody
def Loop.program : Loop→ProgHOL 64
  | .block32=>Copy32.loop32 | .word=>Copy32.loopWord | .bytes=>Copy32.loopBytes | .tail=>Copy32.loopTail

theorem Loop.shape (loop : Loop) : loop.program=.while loop.zeroLoop.test loop.block := by
  cases loop
  · exact CopyWords.loop_shapes.1
  · exact CopyWords.loop_shapes.2
  · exact CopyBytes.loop_shapes.1
  · exact CopyBytes.loop_shapes.2

theorem Loop.block_model (loop : Loop) (code) : Copy32Flow.Block code loop.block loop.stride := by
  cases loop with
  | block32=>exact Copy32Flow.word_stores code _ _ 32 (Copy32Flow.increment code 32)
  | word=>exact Copy32Flow.word_stores code _ _ 8 (Copy32Flow.increment code 8)
  | bytes=>exact Copy32Flow.byte_stores code _ _ 8 (Copy32Flow.increment code 8)
  | tail=>exact Copy32Flow.tail_block code

theorem Loop.cost (loop : Loop) (length : Nat) (small : length+32<2^64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : StrideInvariant length source) :
    source.clock-(evaluateHOLFiniteState source loop.program).2.clock≤length/loop.stride := by
  have block:=loop.block_model source.code
  have priced:=CounterFlow.stride_loop_cost source.code loop.zeroLoop.test loop.block loop.stride length 0
    (by cases loop <;> decide) (by omega) block.advance block.summary (loop.zeroLoop.reads length small)
    (ClockCost.of_quiet source.code _ block.quiet) source rfl valid
  simp only [Nat.zero_add,Nat.one_mul] at priced
  rw [Loop.shape]
  exact priced.trans (Nat.div_le_div_right (Nat.sub_le _ _))

theorem Loop.normal (loop : Loop) (length : Nat) (small : length+32<2^64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : StrideInvariant length source)
    (normal : evaluateHOLFiniteState source loop.program=(none,post)) : StrideInvariant length post := by
  have block:=loop.block_model source.code
  rw [Loop.shape] at normal
  exact CounterFlow.stride_loop_normal source.code loop.zeroLoop.test loop.block loop.stride length
    (by cases loop <;> decide) (by omega) block.advance block.summary (loop.zeroLoop.reads length small) source post rfl valid normal

end InitECandidate.Solver.Input.CopyAny

#print axioms InitECandidate.Solver.Input.CopyAny.Loop.shape
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.block_model
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.cost
#print axioms InitECandidate.Solver.Input.CopyAny.Loop.normal
