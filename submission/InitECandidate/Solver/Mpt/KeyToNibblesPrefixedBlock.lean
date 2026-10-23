import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedReady
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def prefixedByte {F : Type} (source : PanSemStateFiniteExact 64 F) (key : BitVec 64) (index written : Nat) : BitVec 8:=
  ByteRegion.value source (key+BitVec.ofNat 64 index+BitVec.ofNat 64 written)
def prefixedStepState {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (key out : BitVec 64)
    (leading index written : Nat):=
  byteState source name written (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) (prefixedByte source key index written)

theorem PrefixedReady.byte_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) (ready : PrefixedReady source key out leading length index written)
    (name : String) (notOut : ofString "out"≠ofString name) (notIndex : ofString "i"≠ofString name)
    (room : index+written+1≤length) (rest : ProgHOL 64) :
    evaluateHOLFiniteState source (byteStep name written rest)=
      (let output:=evaluateHOLFiniteState (prefixedStepState source name key out leading index written) rest
       (output.1,QueryBranch.restore source name output.2)) := by
  apply KeyToNibbles.byte_execute source name written key (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index)
    (prefixedByte source key index written) rest notOut notIndex ready.keyCell ready.outCell ready.indexCell
    (PrefixedReady.input_byte source key out leading length index written ready (by omega))
  · rw [(prefix_pair_addresses out leading index written).1]
    exact ready.mapped _ (by omega)
  · rw [(prefix_pair_addresses out leading index written).2]
    exact ready.mapped _ (by omega)

theorem PrefixedReady.advance {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) (ready : PrefixedReady source key out leading length index written) :
    PrefixedReady (bind source "i" (BitVec.ofNat 64 (index+written))) key out leading length (index+written) 0 := by
  refine ⟨?_,?_,bind_lookup_same _ _ _,?_,ready.little,by simpa using ready.inside,ready.small,ready.fits,ready.mapped,ready.inputMapped,?_⟩
  · exact (bind_lookup_other _ _ _ _ (by decide)).trans ready.keyCell
  · exact (bind_lookup_other _ _ _ _ (by decide)).trans ready.outCell
  · exact (bind_lookup_other _ _ _ _ (by decide)).trans ready.lengthCell
  · change NibblePrefix source out (leading+2*((index+written)+0))
    simpa only [Nat.add_zero] using ready.nibbles

theorem PrefixedReady.increment_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index written : Nat) (ready : PrefixedReady source key out leading length index written) :
    evaluateHOLFiniteState source (increment (BitVec.ofNat 64 written))=(none,bind source "i" (BitVec.ofNat 64 (index+written))) := by
  have read : eval source (addConst (localVar "i") (BitVec.ofNat 64 written))=some (.val (.word (BitVec.ofNat 64 (index+written)))):=by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,ready.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  exact StateSteps.assign_execute source "i" _ (BitVec.ofNat 64 index) _ ready.indexCell read

/-- Execute the literal four-byte block while reading each byte from its
real current memory. No assumption about future input-byte contents is used. -/
theorem prefixed_block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index : Nat) (ready : PrefixedReady source key out leading length index 0) (room : index+4≤length) :
    ∃ post,evaluateHOLFiniteState source blockBody=(none,post) ∧ PrefixedReady post key out leading length (index+4) 0 ∧ post.clock=source.clock := by
  let first:=prefixedStepState source "b0" key out leading index 0
  have ready1 : PrefixedReady first key out leading length index 1:=
    PrefixedReady.byte source key out leading length index 0 ready "b0" _ (by decide) (by decide) (by decide) (by decide) (by omega)
  let second:=prefixedStepState first "b1" key out leading index 1
  have ready2 : PrefixedReady second key out leading length index 2:=
    PrefixedReady.byte first key out leading length index 1 ready1 "b1" _ (by decide) (by decide) (by decide) (by decide) (by omega)
  let third:=prefixedStepState second "b2" key out leading index 2
  have ready3 : PrefixedReady third key out leading length index 3:=
    PrefixedReady.byte second key out leading length index 2 ready2 "b2" _ (by decide) (by decide) (by decide) (by decide) (by omega)
  let fourth:=prefixedStepState third "b3" key out leading index 3
  have ready4 : PrefixedReady fourth key out leading length index 4:=
    PrefixedReady.byte third key out leading length index 3 ready3 "b3" _ (by decide) (by decide) (by decide) (by decide) (by omega)
  let advanced:=bind fourth "i" (BitVec.ofNat 64 (index+4))
  have incrementRun : evaluateHOLFiniteState fourth (increment 4#64)=(none,advanced):=
    PrefixedReady.increment_execute fourth key out leading length index 4 ready4
  have readyAdvanced : PrefixedReady advanced key out leading length (index+4) 0:=PrefixedReady.advance fourth key out leading length index 4 ready4
  let back3:=restore third "b3" advanced
  have run3 : evaluateHOLFiniteState third (byteStep "b3" 3 (increment 4#64))=(none,back3):=by
    rw [PrefixedReady.byte_execute third key out leading length index 3 ready3 "b3" (by decide) (by decide) (by omega),incrementRun]
  have readyBack3 : PrefixedReady back3 key out leading length (index+4) 0:=
    PrefixedReady.restore third advanced key out leading length (index+4) 0 readyAdvanced "b3" (by decide) (by decide) (by decide) (by decide)
  let back2:=restore second "b2" back3
  have run2 : evaluateHOLFiniteState second (byteStep "b2" 2 (byteStep "b3" 3 (increment 4#64)))=(none,back2):=by
    rw [PrefixedReady.byte_execute second key out leading length index 2 ready2 "b2" (by decide) (by decide) (by omega),run3]
  have readyBack2 : PrefixedReady back2 key out leading length (index+4) 0:=
    PrefixedReady.restore second back3 key out leading length (index+4) 0 readyBack3 "b2" (by decide) (by decide) (by decide) (by decide)
  let back1:=restore first "b1" back2
  have run1 : evaluateHOLFiniteState first (byteStep "b1" 1 (byteStep "b2" 2 (byteStep "b3" 3 (increment 4#64))))=(none,back1):=by
    rw [PrefixedReady.byte_execute first key out leading length index 1 ready1 "b1" (by decide) (by decide) (by omega),run2]
  have readyBack1 : PrefixedReady back1 key out leading length (index+4) 0:=
    PrefixedReady.restore first back2 key out leading length (index+4) 0 readyBack2 "b1" (by decide) (by decide) (by decide) (by decide)
  let post:=restore source "b0" back1
  have steps : blockBody=byteStep "b0" 0 (byteStep "b1" 1 (byteStep "b2" 2 (byteStep "b3" 3 (increment 4#64)))):=by
    rw [block_body_shape]
    rfl
  have run : evaluateHOLFiniteState source blockBody=(none,post):=by
    rw [steps,PrefixedReady.byte_execute source key out leading length index 0 ready "b0" (by decide) (by decide) (by omega),run1]
  exact ⟨post,run,PrefixedReady.restore source back1 key out leading length (index+4) 0 readyBack1 "b0" (by decide) (by decide) (by decide) (by decide),rfl⟩

theorem prefixed_tail_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (leading length index : Nat) (ready : PrefixedReady source key out leading length index 0) (room : index+1≤length) :
    ∃ post,evaluateHOLFiniteState source tailBody=(none,post) ∧ PrefixedReady post key out leading length (index+1) 0 ∧ post.clock=source.clock := by
  let written:=prefixedStepState source "b" key out leading index 0
  have next : PrefixedReady written key out leading length index 1:=
    PrefixedReady.byte source key out leading length index 0 ready "b" _ (by decide) (by decide) (by decide) (by decide) room
  let advanced:=bind written "i" (BitVec.ofNat 64 (index+1))
  have incrementRun : evaluateHOLFiniteState written (increment 1#64)=(none,advanced):=PrefixedReady.increment_execute written key out leading length index 1 next
  have readyAdvanced:=PrefixedReady.advance written key out leading length index 1 next
  refine ⟨restore source "b" advanced,?_,PrefixedReady.restore source advanced key out leading length (index+1) 0 readyAdvanced "b" (by decide) (by decide) (by decide) (by decide),rfl⟩
  rw [tail_body_shape]
  change evaluateHOLFiniteState source (byteStep "b" 0 (increment 1#64))=_
  rw [PrefixedReady.byte_execute source key out leading length index 0 ready "b" (by decide) (by decide) room,incrementRun]

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.byte_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.advance
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.PrefixedReady.increment_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefixed_block_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefixed_tail_execute
