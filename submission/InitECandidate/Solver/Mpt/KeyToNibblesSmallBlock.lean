import InitECandidate.Solver.Mpt.KeyToNibblesSmallFootprint
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem small_block_steps : blockBody = byteStep "b0" 0 (byteStep "b1" 1 (byteStep "b2" 2 (byteStep "b3" 3 (increment 4#64)))) := by
  rw [block_body_shape]
  rfl

theorem SmallReady.byte_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes)
    (name : String) (notOut : ofString "out" ≠ ofString name) (notIndex : ofString "i" ≠ ofString name)
    (room : index + written + 1 ≤ length) (rest : ProgHOL 64) :
    evaluateHOLFiniteState source (byteStep name written rest) =
      (let output := evaluateHOLFiniteState (byteState source name written out (BitVec.ofNat 64 index) (bytes (index + written))) rest
       (output.1, WitnessRadix.QueryBranch.restore source name output.2)) := by
  apply KeyToNibbles.byte_execute source name written key out (BitVec.ofNat 64 index) (bytes (index + written)) rest
    notOut notIndex ready.keyCell ready.outCell ready.indexCell (SmallReady.input_byte source key out length index written bytes ready (by omega))
  · rw [(pair_addresses out index written).1]
    exact ready.mapped _ (by omega)
  · rw [(pair_addresses out index written).2]
    exact ready.mapped _ (by omega)

theorem SmallReady.advance {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes) :
    SmallReady (bind source "i" (BitVec.ofNat 64 (index + written))) key out length (index + written) 0 bytes := by
  refine ⟨?_, ?_, bind_lookup_same _ _ _, ?_, ready.little, by simpa using ready.inside, ready.small,
    ready.fits, ready.mapped, ready.input, ready.separate, ?_⟩
  · exact (bind_lookup_other _ _ _ _ (by decide)).trans ready.keyCell
  · exact (bind_lookup_other _ _ _ _ (by decide)).trans ready.outCell
  · exact (bind_lookup_other _ _ _ _ (by decide)).trans ready.lengthCell
  · change NibblePrefix source out (2 * (index + written))
    exact ready.nibbles

theorem SmallReady.increment_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (length index written : Nat) (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index written bytes) :
    evaluateHOLFiniteState source (increment (BitVec.ofNat 64 written)) =
      (none, bind source "i" (BitVec.ofNat 64 (index + written))) := by
  have read : eval source (addConst (localVar "i") (BitVec.ofNat 64 written)) =
      some (.val (.word (BitVec.ofNat 64 (index + written)))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, ready.indexCell,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.ofNat_add]
  exact StateSteps.assign_execute source "i" _ (BitVec.ofNat 64 index) _ ready.indexCell read

/-- The full unchanged four-input-byte/eight-output-nibble body, from
current input/separation/mapping facts. No later normal body is a premise. -/
theorem small_block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64) (length index : Nat)
    (bytes : Nat → BitVec 8) (ready : SmallReady source key out length index 0 bytes) (room : index + 4 ≤ length) :
    ∃ post, evaluateHOLFiniteState source blockBody = (none, post) ∧ SmallReady post key out length (index + 4) 0 bytes ∧
      post.clock = source.clock ∧ OutputFrame source post out := by
  let first := byteState source "b0" 0 out (BitVec.ofNat 64 index) (bytes (index + 0))
  have ready1 : SmallReady first key out length index 1 bytes :=
    SmallReady.byte source key out length index 0 bytes ready "b0" (by decide) (by decide) (by decide) (by decide) (by omega)
  let second := byteState first "b1" 1 out (BitVec.ofNat 64 index) (bytes (index + 1))
  have ready2 : SmallReady second key out length index 2 bytes :=
    SmallReady.byte first key out length index 1 bytes ready1 "b1" (by decide) (by decide) (by decide) (by decide) (by omega)
  let third := byteState second "b2" 2 out (BitVec.ofNat 64 index) (bytes (index + 2))
  have ready3 : SmallReady third key out length index 3 bytes :=
    SmallReady.byte second key out length index 2 bytes ready2 "b2" (by decide) (by decide) (by decide) (by decide) (by omega)
  let fourth := byteState third "b3" 3 out (BitVec.ofNat 64 index) (bytes (index + 3))
  have ready4 : SmallReady fourth key out length index 4 bytes :=
    SmallReady.byte third key out length index 3 bytes ready3 "b3" (by decide) (by decide) (by decide) (by decide) (by omega)
  let advanced := bind fourth "i" (BitVec.ofNat 64 (index + 4))
  have incrementRun : evaluateHOLFiniteState fourth (increment 4#64) = (none, advanced) :=
    SmallReady.increment_execute fourth key out length index 4 bytes ready4
  have readyAdvanced : SmallReady advanced key out length (index + 4) 0 bytes := SmallReady.advance fourth key out length index 4 bytes ready4
  let back3 := restore third "b3" advanced
  have run3 : evaluateHOLFiniteState third (byteStep "b3" 3 (increment 4#64)) = (none, back3) := by
    rw [SmallReady.byte_execute third key out length index 3 bytes ready3 "b3" (by decide) (by decide) (by omega), incrementRun]
  have readyBack3 : SmallReady back3 key out length (index + 4) 0 bytes :=
    SmallReady.restore third advanced key out length (index + 4) 0 bytes readyAdvanced "b3" (by decide) (by decide) (by decide) (by decide)
  let back2 := restore second "b2" back3
  have run2 : evaluateHOLFiniteState second (byteStep "b2" 2 (byteStep "b3" 3 (increment 4#64))) = (none, back2) := by
    rw [SmallReady.byte_execute second key out length index 2 bytes ready2 "b2" (by decide) (by decide) (by omega), run3]
  have readyBack2 : SmallReady back2 key out length (index + 4) 0 bytes :=
    SmallReady.restore second back3 key out length (index + 4) 0 bytes readyBack3 "b2" (by decide) (by decide) (by decide) (by decide)
  let back1 := restore first "b1" back2
  have run1 : evaluateHOLFiniteState first (byteStep "b1" 1 (byteStep "b2" 2 (byteStep "b3" 3 (increment 4#64)))) = (none, back1) := by
    rw [SmallReady.byte_execute first key out length index 1 bytes ready1 "b1" (by decide) (by decide) (by omega), run2]
  have readyBack1 : SmallReady back1 key out length (index + 4) 0 bytes :=
    SmallReady.restore first back2 key out length (index + 4) 0 bytes readyBack2 "b1" (by decide) (by decide) (by decide) (by decide)
  let post := restore source "b0" back1
  have run : evaluateHOLFiniteState source blockBody = (none, post) := by
    rw [small_block_steps, SmallReady.byte_execute source key out length index 0 bytes ready "b0" (by decide) (by decide) (by omega), run1]
  have readyPost : SmallReady post key out length (index + 4) 0 bytes :=
    SmallReady.restore source back1 key out length (index + 4) 0 bytes readyBack1 "b0" (by decide) (by decide) (by decide) (by decide)
  refine ⟨post, run, readyPost, rfl, ⟨rfl, ?_⟩⟩
  intro query outside
  change fourth.memory query = source.memory query
  calc
    fourth.memory query = third.memory query := SmallReady.byte_memory third key out query length index 3 bytes ready3 "b3" (by omega) outside
    _ = second.memory query := SmallReady.byte_memory second key out query length index 2 bytes ready2 "b2" (by omega) outside
    _ = first.memory query := SmallReady.byte_memory first key out query length index 1 bytes ready1 "b1" (by omega) outside
    _ = source.memory query := SmallReady.byte_memory source key out query length index 0 bytes ready "b0" (by omega) outside

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_block_steps
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.byte_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.advance
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SmallReady.increment_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_block_execute
