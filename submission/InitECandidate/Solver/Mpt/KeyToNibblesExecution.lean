import InitECandidate.Solver.Mpt.KeyToNibblesLoop

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete original 32-byte key conversion. Actual output bytes supply
the trie walk's KeyView; the two original loops spend exactly eight source
ticks. Source mapped input and separate mapped output are current facts. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (bytes : Nat → BitVec 8)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (mapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (input : ByteRegion.Reads source key 32 bytes)
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (enough : 8 ≤ source.clock) :
    ∃ post, evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), post) ∧
      TrieWalk.KeyView post.memory post.memaddrs post.be out 64 ∧ post.clock = source.clock - 8 ∧ OutputFrame source post out := by
  let entered := bind source "i" 0#64
  have ready : Ready entered key out 0 0 bytes := by
    refine ⟨?_, ?_, bind_lookup_same _ _ _, ?_, little, by decide, fits, mapped, input, separate, ?_⟩
    · exact (bind_lookup_other source "i" "key" 0#64 (by decide)).trans keyCell
    · exact (bind_lookup_other source "i" "out" 0#64 (by decide)).trans outCell
    · exact (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell
    · intro offset impossible
      omega
  obtain ⟨afterBlocks, loopRun, finalReady, clockEq, loopFrame⟩ := block_loop_execute entered key out 0 bytes ready (by decide) enough
  have tailTest : eval afterBlocks tailCondition = some (.val (.word 0#64)) := by
    simp [tailCondition, eval, evalHOLExact, localVar, toExact, finalReady.indexCell, finalReady.lengthCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have tailRun : evaluateHOLFiniteState afterBlocks (.seq tailLoop afterTail) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite afterBlocks) := by
    rw [loop_shapes.2, MutableTable.MemeqByteRuntime.loop_stop afterBlocks tailCondition tailBody afterTail tailTest, after_tail_shape]
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have innerRun : evaluateHOLFiniteState entered (.seq blockLoop (.seq tailLoop afterTail)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite afterBlocks) := by
    rw [evaluateHOLFiniteState_seq_line780, loopRun]
    exact tailRun
  have whole := Input.ScalarScope.declare_execute source (emptyLocalsHOLFinite afterBlocks) "i" (.const 0#64) 0#64 _
    (some (.returned (.val (.word 0#64)))) (by rfl) innerRun
  rw [← body_shape] at whole
  refine ⟨restore source "i" (emptyLocalsHOLFinite afterBlocks), whole, ?_, ?_, ⟨loopFrame.fields, loopFrame.memory⟩⟩
  · exact NibblePrefix.key_view afterBlocks out finalReady.fits finalReady.mapped finalReady.nibbles
  · change afterBlocks.clock = source.clock - 8
    change afterBlocks.clock = source.clock - (32 - 0) / 4 at clockEq
    simpa only [Nat.sub_zero, Nat.reduceDiv] using clockEq

theorem execute_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (enough : 8 ≤ source.clock) :
    ∃ post, evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), post) ∧
      TrieWalk.KeyView post.memory post.memaddrs post.be out 64 ∧ post.clock = source.clock - 8 ∧ OutputFrame source post out :=
  execute source key out (fun offset => ByteRegion.value source (byteAddress key offset)) keyCell outCell lengthCell little fits outputMapped
    (ByteRegion.mapped_region source key 32 inputMapped) separate enough

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.execute_mapped
