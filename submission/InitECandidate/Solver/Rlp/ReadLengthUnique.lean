import InitECandidate.Solver.Rlp.ReadLengthStep

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def BytesAgree (left right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) : Prop :=
  ∀ offset : BitVec 64, offset.toNat<length.toNat → byte left (pointer+offset)=byte right (pointer+offset)

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length index value : BitVec 64) (view : Locals source pointer length index value) :
    eval source condition=some (.val (.word (if index.toNat<length.toNat then 1#64 else 0#64))) := by
  simp [condition,eval,evalHOLExact,localVar,toExact,view.indexCell,view.lengthCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

/-- Only bytes selected by actual active iterations need agree. Both runs
are actual successful executions; their clocks, other locals, globals and
FFI state need not match. -/
theorem loop_unique (left right leftPost rightPost : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length index value : BitVec 64)
    (leftView : Locals left pointer length index value) (rightView : Locals right pointer length index value)
    (bytes : BytesAgree left right pointer length)
    (leftRun : evaluateHOLFiniteState left loop=(none,leftPost))
    (rightRun : evaluateHOLFiniteState right loop=(none,rightPost)) :
    leftPost.locals.lookup (ofString "v")=rightPost.locals.lookup (ofString "v") := by
  classical
  have auxiliary : ∀ clock (left right leftPost rightPost : PanSemStateFiniteExact 64 Guest.HostMemory)
      (pointer length index value : BitVec 64), left.clock=clock →
      Locals left pointer length index value → Locals right pointer length index value →
      BytesAgree left right pointer length →
      evaluateHOLFiniteState left loop=(none,leftPost) → evaluateHOLFiniteState right loop=(none,rightPost) →
      leftPost.locals.lookup (ofString "v")=rightPost.locals.lookup (ofString "v") := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro left right leftPost rightPost pointer length index value clockEq leftView rightView bytes leftRun rightRun
      have leftRead := condition_read left pointer length index value leftView
      have rightRead := condition_read right pointer length index value rightView
      by_cases active : index.toNat<length.toNat
      · rw [if_pos active] at leftRead rightRead
        have leftLoop := leftRun
        have rightLoop := rightRun
        rw [loop_shape] at leftLoop rightLoop
        obtain ⟨leftPositive,leftMiddle,leftBody,leftTail,leftClock⟩ :=
          Input.while_none_step left leftPost (ofString "n") condition loopBody loop_body_limit leftRead leftLoop
        obtain ⟨rightPositive,rightMiddle,rightBody,rightTail,rightClock⟩ :=
          Input.while_none_step right rightPost (ofString "n") condition loopBody loop_body_limit rightRead rightLoop
        have leftEntry : Locals (decClockHOLFinite left) pointer length index value :=
          ⟨leftView.pointerCell,leftView.lengthCell,leftView.indexCell,leftView.valueCell⟩
        have rightEntry : Locals (decClockHOLFinite right) pointer length index value :=
          ⟨rightView.pointerCell,rightView.lengthCell,rightView.indexCell,rightView.valueCell⟩
        obtain ⟨leftByte,leftByteRead,leftEq⟩ := step_none (decClockHOLFinite left) leftMiddle pointer length index value leftEntry leftBody
        obtain ⟨rightByte,rightByteRead,rightEq⟩ := step_none (decClockHOLFinite right) rightMiddle pointer length index value rightEntry rightBody
        have byteEq : leftByte=rightByte := Option.some.inj (leftByteRead.symm.trans ((bytes index active).trans rightByteRead))
        subst rightByte
        have nextLeft := step_locals (decClockHOLFinite left) pointer length index value leftByte leftEntry
        have nextRight := step_locals (decClockHOLFinite right) pointer length index value leftByte rightEntry
        rw [←leftEq] at nextLeft
        rw [←rightEq] at nextRight
        have nextBytes : BytesAgree leftMiddle rightMiddle pointer length := by
          intro offset inside
          rw [leftEq,rightEq]
          exact bytes offset inside
        have smaller : leftMiddle.clock<clock := by omega
        rw [←loop_shape] at leftTail rightTail
        exact ih leftMiddle.clock smaller leftMiddle rightMiddle leftPost rightPost pointer length (index+1#64)
          ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 leftByte.toNat) rfl nextLeft nextRight nextBytes leftTail rightTail
      · rw [if_neg active] at leftRead rightRead
        have leftEq : leftPost=left := by
          rw [loop_shape,evaluateHOLFiniteState_while_total] at leftRun
          change evalHOLFinite left (h:=fun query=>Classical.propDecidable (left.memaddrs query)) condition=some (.val (.word 0#64)) at leftRead
          rw [leftRead] at leftRun
          simpa using (congrArg Prod.snd leftRun).symm
        have rightEq : rightPost=right := by
          rw [loop_shape,evaluateHOLFiniteState_while_total] at rightRun
          change evalHOLFinite right (h:=fun query=>Classical.propDecidable (right.memaddrs query)) condition=some (.val (.word 0#64)) at rightRead
          rw [rightRead] at rightRun
          simpa using (congrArg Prod.snd rightRun).symm
        rw [leftEq,rightEq,leftView.valueCell,rightView.valueCell]
  exact auxiliary left.clock left right leftPost rightPost pointer length index value rfl leftView rightView bytes leftRun rightRun

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.condition_read
#print axioms InitECandidate.Solver.Rlp.ReadLength.loop_unique
