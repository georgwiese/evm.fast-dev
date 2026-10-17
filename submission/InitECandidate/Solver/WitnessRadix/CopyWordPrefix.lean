import InitECandidate.Solver.WitnessRadix.CopyContext

namespace InitECandidate.Solver.WitnessRadix.CopyWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch CopyContext

def wordOffsets : List Nat := [0,8,16,24]
def prefixCost (length : Nat) : Nat := length/32 + (length%32)/8
def prefixIndex (length : Nat) : Nat := 32*(length/32) + 8*((length%32)/8)
def prefixState {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) : PanSemStateFiniteExact 64 F :=
  walk (walk source src dst 0 32 wordOffsets (length/32)) src dst (32*(length/32)) 8 [0] ((length%32)/8)

theorem prefix_bounds (length : Nat) : prefixIndex length ≤ length ∧ length < prefixIndex length + 8 ∧ prefixCost length ≤ prefixIndex length := by
  have h1 := Nat.mod_add_div length 32
  have h2 := Nat.mod_add_div (length%32) 8
  have h3 := Nat.mod_lt (length%32) (by decide : 0 < 8)
  simp only [prefixIndex, prefixCost]
  omega

theorem prefix_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (args : Args source src dst length) (mapped : Mapped source src dst length)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (mask : (dst ||| src) &&& 7#64 = 0#64) (small : length + 32 < 2 ^ 64) (enough : prefixCost length ≤ source.clock) :
    evaluateHOLFiniteState source (.seq Copy32.loop32 Copy32.loopWord) = (none, prefixState source src dst length) := by
  classical
  let rounds := length/32
  let afterIndex := 32*rounds
  let after32 := walk source src dst 0 32 wordOffsets rounds
  have div := Nat.mod_add_div length 32
  have rem := Nat.mod_lt length (by decide : 0 < 32)
  have div8 := Nat.mod_add_div (length%32) 8
  have rem8 := Nat.mod_lt (length%32) (by decide : 0 < 8)
  have blockRun := loop_execute source src dst false 32 0 length rounds wordOffsets (by decide) (by decide)
    (by intro h; contradiction) (by intro offset member; simp [wordOffsets] at member; omega)
    (by decide) (by decide)
    (by intro offset member; simp [wordOffsets] at member; rcases member with rfl | rfl | rfl | rfl <;> decide)
    small (by dsimp [rounds]; omega) (by dsimp [rounds]; omega)
    args.srcLocal args.dstLocal indexLocal args.lengthLocal
    (by intro offset low high aligned; exact mapped.sourceWords mask offset high aligned)
    (by intro offset low high aligned; exact mapped.destinationWords mask offset high aligned)
    (by unfold prefixCost at enough; dsimp [rounds]; omega)
  have blockExact : evaluateHOLFiniteState source Copy32.loop32 = (none, after32) := by
    rw [loop_shapes.1]
    exact blockRun
  have afterArgs := Args.word_walk source src dst length 0 32 rounds wordOffsets args
  have afterMapped := Mapped.of_domain source after32 src dst length (word_walk_domain source src dst 0 32 rounds wordOffsets) mapped
  have afterLocal : after32.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 afterIndex))) := by
    simpa only [Nat.zero_add] using walk_index source src dst 0 32 wordOffsets rounds indexLocal
  have afterClock : after32.clock = source.clock - rounds := word_walk_clock source src dst 0 32 rounds wordOffsets
  have wordRun := loop_execute after32 src dst false 8 afterIndex length ((length%32)/8) [0] (by decide) (by decide)
    (by intro h; contradiction) (by intro offset member; simp at member; omega)
    (by decide) (by dsimp [afterIndex]; omega)
    (by intro offset member; simp at member; subst offset; decide)
    small (by dsimp [afterIndex, rounds]; omega) (by dsimp [afterIndex, rounds]; omega)
    afterArgs.srcLocal afterArgs.dstLocal afterLocal afterArgs.lengthLocal
    (by intro offset low high aligned; exact afterMapped.sourceWords mask offset high aligned)
    (by intro offset low high aligned; exact afterMapped.destinationWords mask offset high aligned)
    (by rw [afterClock]; unfold prefixCost at enough; dsimp [rounds]; omega)
  have wordExact : evaluateHOLFiniteState after32 Copy32.loopWord = (none, prefixState source src dst length) := by
    rw [loop_shapes.2]
    exact wordRun
  exact (StateSteps.next_sequence source after32 _ _ blockExact (by rw [afterClock]; omega)).trans wordExact

theorem prefix_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat) :
    (prefixState source src dst length).clock = source.clock - prefixCost length := by
  simp only [prefixState, word_walk_clock, prefixCost]
  omega

theorem prefix_index {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (initial : source.locals.lookup (ofString "i") = some (.val (.word 0#64))) :
    (prefixState source src dst length).locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (prefixIndex length)))) := by
  apply walk_index
  simpa only [Nat.zero_add] using walk_index source src dst 0 32 wordOffsets (length/32) initial

end InitECandidate.Solver.WitnessRadix.CopyWords

#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.prefix_bounds
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.prefix_execute
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.prefix_clock
#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.prefix_index
