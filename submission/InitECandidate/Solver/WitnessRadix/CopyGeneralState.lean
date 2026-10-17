import InitECandidate.Solver.WitnessRadix.CopyByteSuffix
import InitECandidate.Solver.WitnessRadix.CopyWordPrefix

namespace InitECandidate.Solver.WitnessRadix.CopyContext
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def control {F : Type} (source : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite { source with memory := fun _ => .word 0#64, clock := 0 }

theorem control_of_frame {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with memory := target.memory, clock := target.clock }) :
    control target = control source := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with memory := fun _ => .word 0#64, clock := 0 }) frame
  exact h

theorem frame_of_control {F : Type} (source target : PanSemStateFiniteExact 64 F) (same : control target = control source) :
    emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with memory := target.memory, clock := target.clock } := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with memory := target.memory, clock := target.clock }) same
  exact h

theorem byte_walk_control {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    control (CopyBytes.walk source src dst index step offsets rounds) = control source := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with memory := fun _ => .word 0#64, clock := 0 })
    (CopyBytes.walk_frame source src dst index step offsets rounds)
  exact h

theorem word_walk_control {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    control (CopyWords.walk source src dst index step offsets rounds) = control source := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with memory := fun _ => .word 0#64, clock := 0 })
    (CopyWords.walk_frame source src dst index step offsets rounds)
  exact h

theorem prefix_args {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (args : Args source src dst length) : Args (CopyWords.prefixState source src dst length) src dst length :=
  Args.word_walk _ _ _ _ _ _ _ _ (Args.word_walk _ _ _ _ _ _ _ _ args)

theorem prefix_domain {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    (CopyWords.prefixState source src dst length).memaddrs = source.memaddrs := by
  simp only [CopyWords.prefixState, word_walk_domain]

theorem prefix_control {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    control (CopyWords.prefixState source src dst length) = control source := by
  simp only [CopyWords.prefixState, word_walk_control]

theorem suffix_control {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index length : Nat) :
    control (CopyBytes.suffixState source src dst index length) = control source := by
  simp only [CopyBytes.suffixState, byte_walk_control]

theorem suffix_cost_le (index length : Nat) : CopyBytes.suffixCost index length ≤ length-index := by
  have div := Nat.mod_add_div (length-index) 8
  unfold CopyBytes.suffixCost
  omega

end InitECandidate.Solver.WitnessRadix.CopyContext

#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.control_of_frame
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.frame_of_control
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.byte_walk_control
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.word_walk_control
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.prefix_args
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.prefix_domain
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.prefix_control
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.suffix_control
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.suffix_cost_le
