import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.CopyCostBounds
import InitECandidate.Solver.WitnessRadix.CopyGeneralCall
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString CopyContext

/-- Whole-word lengths have no byte tail, even on the unaligned path. -/
theorem cost_word_multiple (src dst : BitVec 64) (length : Nat) (multiple : length%8=0) :
    cost src dst length≤length/8 := by
  by_cases mask : aligned src dst
  · rw [cost_aligned src dst length mask]
    have d32 := Nat.mod_add_div length 32
    have d8 := Nat.mod_add_div (length%32) 8
    have d := Nat.mod_add_div length 8
    omega
  · rw [cost,if_neg mask,CopyBytes.suffixCost,Nat.sub_zero,multiple,Nat.add_zero]
    exact Nat.le_refl _

/-- The unchanged memcpy at its actual mapped operands, with every clock
budget covered. Sufficient funding gives its exact execution; otherwise its
initial clock already bounds all possible spent ticks. -/
theorem call_cost {F : Type} (source : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (formals,Copy32.body,.one))
    (mapped : Mapped source src dst length) (small : length+32<2^64) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock≤cost src dst length+1 := by
  by_cases enough : cost src dst length+1≤source.clock
  · rw [call_execute source arguments src dst length args code mapped small enough]
    change source.clock-(source.clock-(cost src dst length+1))≤cost src dst length+1
    omega
  · have spent := Nat.sub_le source.clock (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock
    omega

/-- Actual original32/8/byte loop counts give an alignment-independent
linear bound; the real encoded byte length is charged only once. -/
theorem call_cost_blocks {F : Type} (source : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (formals,Copy32.body,.one))
    (mapped : Mapped source src dst length) (small : length+32<2^64) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock≤length/8+8 := by
  have actual := call_cost source arguments src dst length args code mapped small
  have blocks := cost_blocks src dst length
  omega

theorem call_cost_arena {F : Type} (source : PanSemStateFiniteExact 64 F) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values dst src length))
    (code : source.code.lookup (ofString "memcpy")=some (formals,Copy32.body,.one))
    (domain : source.memaddrs=InitE.ordinaryDomain) (srcArena : AllocatedBytes.Arena src length) (dstArena : AllocatedBytes.Arena dst length) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)).2.clock≤cost src dst length+1 := by
  exact call_cost source arguments src dst length args code (AllocatedBytes.copy_mapped source src dst length domain srcArena dstArena)
    (by have upper := srcArena.upper; omega)

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.cost_word_multiple
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_cost
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_cost_blocks
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.call_cost_arena
