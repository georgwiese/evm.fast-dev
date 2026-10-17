import InitECandidate.Solver.WitnessRadix.Keccak256Padding

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem after_blocks_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer scratch out : BitVec 64) (index length : Nat)
    (args : Args source stp pointer length)
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (small : length<2^64) (ordered : index≤length) (remBound : length-index<136)
    (data : TailData source stp pointer scratch out index (length-index)) (enough : 194≤source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source afterBlocks=(some (.returned (.val (.word 0#64))),output) ∧
      output.clock≤source.clock ∧ source.clock-194≤output.clock ∧ KeccakAbsorb.hashControl output=KeccakAbsorb.hashControl source ∧
      ∀ query,Away stp scratch out query → output.memory query=source.memory query := by
  classical
  let entered := bind source "rem" (BitVec.ofNat 64 (length-index))
  have sub : BitVec.ofNat 64 length-BitVec.ofNat 64 index=BitVec.ofNat 64 (length-index) :=
    BitVec.ofNat_sub_ofNat_of_le length index (by omega) ordered
  have read : eval source remainder=some (.val (.word (BitVec.ofNat 64 (length-index)))) := by
    simp [eval,remainder,localVar,evalHOLExact,evalListHOLExact,toExact,args.lengthLocal,indexLocal,valueIsWord,valueWord,wordOpHOL,wordOp,sub]
  have enteredLocals : TailLocals entered stp pointer out index (length-index) := by
    constructor
    · exact (bind_lookup_other source "rem" "stp" _ (by decide)).trans args.stateLocal
    · exact (bind_lookup_other source "rem" "p" _ (by decide)).trans args.pointerLocal
    · exact (bind_lookup_other source "rem" "out" _ (by decide)).trans outLocal
    · exact (bind_lookup_other source "rem" "i" _ (by decide)).trans indexLocal
    · exact bind_lookup_same source "rem" _
  have enteredData := TailData.of_control source entered stp pointer scratch out index (length-index) rfl data
  obtain ⟨output,run,upper,lower,control,memory⟩ := padding_execute entered stp pointer scratch out index (length-index)
    enteredLocals enteredData remBound enough
  refine ⟨restore source "rem" output,?_,upper,lower,?_,memory⟩
  · simp only [eval] at read
    rw [afterBlocks_shape,evaluateHOLFiniteState_dec_total]
    simp only [read,shapeOfHOLExact,shapeEqHOL,↓reduceIte]
    change (let result := (evaluateHOLFiniteState entered paddingTail)
      (result.1,restore source "rem" result.2))=_
    rw [run]
  · exact (KeccakAbsorb.hashControl_restore source output "rem").trans control

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.after_blocks_execute
