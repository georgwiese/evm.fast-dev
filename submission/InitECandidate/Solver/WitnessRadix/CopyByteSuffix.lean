import InitECandidate.Solver.WitnessRadix.CopyContext

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch CopyContext

def byteOffsets : List Nat := [0,1,2,3,4,5,6,7]
def suffixCost (index length : Nat) : Nat := (length - index) / 8 + (length - index) % 8
def suffixState {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index length : Nat) : PanSemStateFiniteExact 64 F :=
  walk (walk source src dst index 8 byteOffsets ((length-index)/8)) src dst
    (index + 8*((length-index)/8)) 1 [0] ((length-index)%8)

theorem suffix_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index length : Nat)
    (args : Args source src dst length) (mapped : Mapped source src dst length)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (ordered : index ≤ length) (small : length + 32 < 2 ^ 64) (enough : suffixCost index length ≤ source.clock) :
    evaluateHOLFiniteState source (.seq Copy32.loopBytes (.seq Copy32.loopTail (.return (.const 0#64)))) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite (suffixState source src dst index length)) := by
  classical
  let rounds := (length-index)/8
  let afterIndex := index + 8*rounds
  let afterBytes := walk source src dst index 8 byteOffsets rounds
  have div := Nat.mod_add_div (length-index) 8
  have rem := Nat.mod_lt (length-index) (by decide : 0 < 8)
  have total : afterIndex + (length-index)%8 = length := by dsimp [afterIndex, rounds]; omega
  have blockRun := loop_execute source src dst false 8 index length rounds byteOffsets (by decide) (by decide)
    (by intro h; contradiction) (by intro offset member; simp [byteOffsets] at member; omega)
    small (by dsimp [rounds]; omega) (by dsimp [rounds]; omega)
    args.srcLocal args.dstLocal indexLocal args.lengthLocal
    (by intro offset low high; exact mapped.sourceBytes offset high)
    (by intro offset low high; exact mapped.destinationBytes offset high)
    (by unfold suffixCost at enough; dsimp [rounds]; omega)
  have blockExact : evaluateHOLFiniteState source Copy32.loopBytes = (none, afterBytes) := by
    rw [loop_shapes.1]
    exact blockRun
  have afterArgs := Args.byte_walk source src dst length index 8 rounds byteOffsets args
  have afterMapped := Mapped.of_domain source afterBytes src dst length (byte_walk_domain source src dst index 8 rounds byteOffsets) mapped
  have afterLocal : afterBytes.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 afterIndex))) :=
    walk_index source src dst index 8 byteOffsets rounds indexLocal
  have afterClock : afterBytes.clock = source.clock - rounds := byte_walk_clock source src dst index 8 rounds byteOffsets
  have tailRun := loop_execute afterBytes src dst true 1 afterIndex length ((length-index)%8) [0] (by decide) (by decide)
    (by intro h; rfl) (by intro offset member; simpa using member)
    small (by omega) (by omega)
    afterArgs.srcLocal afterArgs.dstLocal afterLocal afterArgs.lengthLocal
    (by intro offset low high; exact afterMapped.sourceBytes offset high)
    (by intro offset low high; exact afterMapped.destinationBytes offset high)
    (by rw [afterClock]; unfold suffixCost at enough; dsimp [rounds]; omega)
  have tailExact : evaluateHOLFiniteState afterBytes Copy32.loopTail = (none, suffixState source src dst index length) := by
    rw [loop_shapes.2]
    exact tailRun
  have finalClock : (suffixState source src dst index length).clock ≤ afterBytes.clock := by
    change (walk afterBytes src dst afterIndex 1 [0] ((length-index)%8)).clock ≤ afterBytes.clock
    rw [byte_walk_clock]
    exact Nat.sub_le _ _
  rw [StateSteps.next_sequence source afterBytes _ _ blockExact (by rw [afterClock]; omega),
    StateSteps.next_sequence afterBytes (suffixState source src dst index length) _ _ tailExact finalClock]
  simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]

theorem suffix_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index length : Nat) :
    (suffixState source src dst index length).clock = source.clock - suffixCost index length := by
  simp only [suffixState, byte_walk_clock, suffixCost]
  omega

end InitECandidate.Solver.WitnessRadix.CopyBytes

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.suffix_execute
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.suffix_clock
