import InitECandidate.Solver.WitnessRadix.ScatterCursors
import InitECandidate.Solver.WitnessRadix.BuildCopyPost

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem writeWords_copy (memory : WordScatter.Memory) (dst : BitVec 64)
    (start : Nat) (input : List (BitVec 64)) :
    WordScatter.writeWords (wordAddress dst) memory start input =
      BuildCopy.copyMemory memory dst 0#64 start input := by
  induction input generalizing memory start with
  | nil => rfl
  | cons value rest ih =>
      simp only [WordScatter.writeWords, BuildCopy.copyMemory, ih, wordAddress, BuildCopy.row, BitVec.zero_add]

/-- End-to-end stable partition for the actual helper's scatter loop: exact
filtered block writes, exact source-clock payment and final cursor values. -/
theorem loop_partition {F : Type} (input : List (BitVec 64))
    (source : PanSemStateFiniteExact 64 F) (src dst start keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (position index count zero one limit : Nat)
    (inside : position < 256) (small : count < 2 ^ 64) (size : index + input.length = count)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (keysLocal : source.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (bitLocal : source.locals.lookup (ofString "bit") = some (.val (.word (BitVec.ofNat 64 position))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))))
    (zeroLocal : source.locals.lookup (ofString "zero_cursor") = some (.val (.word (BitVec.ofNat 64 zero))))
    (oneLocal : source.locals.lookup (ofString "one_cursor") = some (.val (.word (BitVec.ofNat 64 one))))
    (ready : Ready source src dst start keys keyFor input index limit)
    (zeroRoom : zero + zeros keyFor position input ≤ limit)
    (oneRoom : one + ones keyFor position input ≤ limit)
    (separate : ∀ i < zeros keyFor position input, ∀ j < ones keyFor position input,
      wordAddress dst (zero + i) ≠ wordAddress dst (one + j))
    (enough : input.length ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source scatterLoop = (none, target) ∧
      target.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 count))) ∧
      target.locals.lookup (ofString "zero_cursor") =
        some (.val (.word (BitVec.ofNat 64 (zero + zeros keyFor position input)))) ∧
      target.locals.lookup (ofString "one_cursor") =
        some (.val (.word (BitVec.ofNat 64 (one + ones keyFor position input)))) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with
        memory := BuildCopy.copyMemory
          (BuildCopy.copyMemory source.memory dst 0#64 zero (input.filter fun ordinal => !keep keyFor position ordinal))
          dst 0#64 one (input.filter (keep keyFor position))
        clock := source.clock - input.length } ∧
      (∀ name : MlS, ofString "i" ≠ name → ofString "zero_cursor" ≠ name → ofString "one_cursor" ≠ name →
        target.locals.lookup name = source.locals.lookup name) := by
  classical
  refine ⟨scatterState source dst keyFor position input index zero one,
    loop_execute input source src dst start keys keyFor position index count zero one limit
      inside small size srcLocal dstLocal startLocal keysLocal bitLocal indexLocal countLocal
      zeroLocal oneLocal ready zeroRoom oneRoom enough,
    ?_, state_zero source dst keyFor position input index zero one zeroLocal,
    state_one source dst keyFor position input index zero one oneLocal, ?_, ?_⟩
  · simpa only [size] using state_index source dst keyFor position input index zero one indexLocal
  · have frame := state_frame source dst keyFor position input index zero one
    rw [WordScatter.scatter_eq_blocks (wordAddress dst) (keep keyFor position) input source.memory zero one separate,
      writeWords_copy, writeWords_copy] at frame
    exact frame
  · intro name notI notZero notOne
    exact state_other source dst keyFor position input index zero one name notI notZero notOne

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.loop_partition
