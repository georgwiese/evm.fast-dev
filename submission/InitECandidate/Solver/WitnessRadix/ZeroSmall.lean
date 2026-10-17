import InitECandidate.Solver.WitnessRadix.ZeroByteState
import InitECandidate.Solver.WitnessRadix.ZeroExecution

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def smallFinalState {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat) :
    PanSemStateFiniteExact 64 F :=
  restore source "i" (emptyLocalsHOLFinite (stateByte (bind source "i" 0#64) dst 0 length))

theorem small_offset (dst : BitVec 64) (offset : Nat) (inside : offset < 8)
    (aligned : dst.toNat % 8 = 0) (fits : dst.toNat + 32 < 2 ^ 64) :
    panByteAlignHOL (width := 64) (byteAddress dst offset) = dst := by
  have head := MemoryBytes.aligned_offset dst offset (by omega) aligned fits
  have division : offset / 8 = 0 := by omega
  simpa [division, byteAddress] using head

/-- Complete fixed memzero for the short aligned ranges, including the
four-byte initial table, via actual byte stores and the real tail loop. -/
theorem execute_small {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat)
    (short : length < 8) (aligned : dst.toNat % 8 = 0) (fits : dst.toNat + 32 < 2 ^ 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : source.memaddrs dst) (enough : length ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), smallFinalState source dst length) := by
  classical
  let initial := bind source "i" 0#64
  let last := stateByte initial dst 0 length
  have initialDst : initial.locals.lookup (ofString "dst") = some (.val (.word dst)) :=
    (bind_lookup_other source "i" "dst" _ (by decide)).trans dstLocal
  have initialLength : initial.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other source "i" "n" _ (by decide)).trans lengthLocal
  have initialIndex : initial.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := bind_lookup_same _ _ _
  have small : length + 32 < 2 ^ 64 := by omega
  have skip32 := loop32_execute initial dst 0 length 0 small (by decide) (by omega) (by omega)
    initialDst initialIndex initialLength (by intro offset _ high _; omega) (Nat.zero_le _)
  have skipWord := loopWord_execute initial dst 0 length 0 small (by decide) (by omega) (by omega)
    initialDst initialIndex initialLength (by intro offset _ high _; omega) (Nat.zero_le _)
  change evaluateHOLFiniteState initial loop32 = (none, initial) at skip32
  change evaluateHOLFiniteState initial loopWord = (none, initial) at skipWord
  have alignedRun : evaluateHOLFiniteState initial (.ite alignment (.seq loop32 loopWord) .skip) = (none, initial) := by
    have test := alignment_read initial dst initialDst aligned
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simp only []
    rw [if_neg (show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide),
      StateSteps.next_sequence initial initial _ _ skip32 (Nat.le_refl _)]
    exact skipWord
  have skipBytes : evaluateHOLFiniteState initial loopBytes = (none, initial) := by
    have test := condition_read initial 0 length 8 small (by omega) (by decide) initialIndex initialLength
    have inactive : ¬ 0 + 8 ≤ length := by omega
    simp only [if_neg inactive] at test
    rw [other_loop_shapes.1, evaluateHOLFiniteState_while_total, test]
    simp
  have tailRun := loopTail_execute initial dst 0 length length (by omega) (Nat.zero_add _)
    initialDst initialIndex initialLength (by
      intro offset _ inside
      rw [small_offset dst offset (by omega) aligned fits]
      exact mapped) enough
  have lastFrame := stateByte_frame initial dst 0 length
  have lastClock : last.clock = source.clock - length := congrArg (fun state => state.clock) lastFrame
  have coreRun : evaluateHOLFiniteState initial
      (.seq (.ite alignment (.seq loop32 loopWord) .skip) (.seq loopBytes (.seq loopTail (.return (.const 0#64))))) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite last) := by
    rw [StateSteps.next_sequence initial initial _ _ alignedRun (Nat.le_refl _),
      StateSteps.next_sequence initial initial _ _ skipBytes (Nat.le_refl _),
      StateSteps.next_sequence initial last _ _ tailRun (by change last.clock ≤ source.clock; omega)]
    exact BuildEntry.zero_return last
  have setup : BuildEntry.Initializes source [("i", .const 0#64)] initial
      (fun target => restore source "i" target) := .step 0#64 rfl (.done _)
  have scope := BuildEntry.declarations_execute setup
    (.seq (.ite alignment (.seq loop32 loopWord) .skip) (.seq loopBytes (.seq loopTail (.return (.const 0#64)))))
  rw [coreRun] at scope
  rw [body_shape]
  exact scope

theorem small_final_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat) :
    emptyLocalsHOLFinite (smallFinalState source dst length) = emptyLocalsHOLFinite { source with
      memory := memoryByte source.memory source.be dst 0 length
      clock := source.clock - length } := by
  exact stateByte_frame (bind source "i" 0#64) dst 0 length

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.execute_small
#print axioms InitECandidate.Solver.WitnessRadix.Zero.small_final_frame
