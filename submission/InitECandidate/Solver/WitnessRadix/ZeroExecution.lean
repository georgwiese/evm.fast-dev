import InitECandidate.Solver.WitnessRadix.ZeroState
import InitECandidate.Solver.WitnessRadix.ZeroTail
import InitECandidate.Solver.PanDeclarations

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def price (length : Nat) : Nat := length / 32 + (length % 32) / 8
def finalState {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat) :
    PanSemStateFiniteExact 64 F :=
  restore source "i" (emptyLocalsHOLFinite
    (stateWord (state32 (bind source "i" 0#64) dst 0 (length / 32)) dst (32 * (length / 32)) ((length % 32) / 8)))

/-- Complete fixed memzero on aligned word-multiple ranges. Both actual
word loops execute, byte loops skip, and lexical scope/return are included. -/
theorem execute_aligned {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (length : Nat)
    (small : length + 32 < 2 ^ 64) (multiple : length % 8 = 0) (aligned : dst.toNat % 8 = 0)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : ∀ offset, offset + 8 ≤ length → offset % 8 = 0 → source.memaddrs (byteAddress dst offset))
    (enough : price length ≤ source.clock) :
    evaluateHOLFiniteState source body =
      (some (.returned (.val (.word 0#64))), finalState source dst length) := by
  classical
  let blocks := length / 32
  let words := (length % 32) / 8
  have total : 32 * blocks + 8 * words = length := by dsimp [blocks, words]; omega
  have stop32 : length < 32 * blocks + 32 := by dsimp [blocks]; omega
  have enough' : blocks + words ≤ source.clock := enough
  let initial := bind source "i" 0#64
  let first := state32 initial dst 0 blocks
  let last := stateWord first dst (32 * blocks) words
  have initialDst : initial.locals.lookup (ofString "dst") = some (.val (.word dst)) :=
    (bind_lookup_other source "i" "dst" _ (by decide)).trans dstLocal
  have initialLength : initial.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (bind_lookup_other source "i" "n" _ (by decide)).trans lengthLocal
  have initialIndex : initial.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 0))) := bind_lookup_same _ _ _
  have firstRun := loop32_execute initial dst 0 length blocks small (by decide) (by omega) (by omega)
    initialDst initialIndex initialLength (by intro offset _ high aligned; exact mapped offset high aligned) (by change blocks ≤ source.clock; omega)
  have firstFrame := state32_frame initial dst 0 blocks
  have firstDomain : first.memaddrs = source.memaddrs := congrArg (fun state => state.memaddrs) firstFrame
  have firstClock : first.clock = source.clock - blocks := congrArg (fun state => state.clock) firstFrame
  have firstDst : first.locals.lookup (ofString "dst") = some (.val (.word dst)) :=
    (state32_other initial dst 0 blocks _ (by decide)).trans initialDst
  have firstLength : first.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (state32_other initial dst 0 blocks _ (by decide)).trans initialLength
  have firstIndex : first.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (32 * blocks)))) := by
    simpa only [Nat.zero_add] using state32_index initial dst 0 blocks initialIndex
  have lastRun := loopWord_execute first dst (32 * blocks) length words small (by omega) (by omega) (by omega)
    firstDst firstIndex firstLength (by intro offset _ high aligned; rw [firstDomain]; exact mapped offset high aligned)
    (by rw [firstClock]; omega)
  have lastFrame := stateWord_frame first dst (32 * blocks) words
  have lastClock : last.clock = first.clock - words := congrArg (fun state => state.clock) lastFrame
  have lastLength : last.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) :=
    (stateWord_other first dst (32 * blocks) words _ (by decide)).trans firstLength
  have lastIndex : last.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 length))) := by
    rw [← total]
    exact stateWord_index first dst (32 * blocks) words firstIndex
  have remaining := remaining_loops last length small lastIndex lastLength
  have chosen : evaluateHOLFiniteState initial (.ite alignment (.seq loop32 loopWord) .skip) = (none, last) := by
    have test := alignment_read initial dst initialDst aligned
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simp only []
    rw [if_neg (show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide)]
    rw [StateSteps.next_sequence initial first _ _ firstRun (by change first.clock ≤ source.clock; omega)]
    exact lastRun
  have tailRun : evaluateHOLFiniteState last (.seq loopBytes (.seq loopTail (.return (.const 0#64)))) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite last) := by
    rw [StateSteps.next_sequence last last _ _ remaining.1 (Nat.le_refl _),
      StateSteps.next_sequence last last _ _ remaining.2 (Nat.le_refl _)]
    exact BuildEntry.zero_return last
  have coreRun := (StateSteps.next_sequence initial last _ _ chosen (by
    change last.clock ≤ source.clock; omega)).trans tailRun
  have setup : BuildEntry.Initializes source [("i", .const 0#64)] initial
      (fun target => restore source "i" target) := .step 0#64 rfl (.done _)
  have scope := BuildEntry.declarations_execute setup
    (.seq (.ite alignment (.seq loop32 loopWord) .skip) (.seq loopBytes (.seq loopTail (.return (.const 0#64)))))
  rw [coreRun] at scope
  rw [body_shape]
  exact scope

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.execute_aligned
