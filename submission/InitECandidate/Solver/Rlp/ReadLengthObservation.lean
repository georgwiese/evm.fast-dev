import InitECandidate.Solver.Rlp.ReadLengthNormal
import InitECandidate.Solver.Rlp.ReadLengthCall
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A past actual successful reader run on these bytes. The witness is
constructed from execution, then transported through proven byte frames. -/
def Observed (reference : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length value : BitVec 64) : Prop :=
  ∃ source post : PanSemStateFiniteExact 64 Guest.HostMemory,
    source.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧
    source.locals.lookup (ofString "n")=some (.val (.word length)) ∧
    Input.OriginalCode.Installed source.code ∧ BytesAgree source reference pointer length ∧
    evaluateHOLFiniteState source body=(some (.returned (.val (.word value))),post)

theorem Observed.transport (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length value : BitVec 64) (observed : Observed source pointer length value)
    (bytes : BytesAgree source target pointer length) : Observed target pointer length value := by
  obtain ⟨entry,post,pointerCell,lengthCell,installed,prior,run⟩ := observed
  exact ⟨entry,post,pointerCell,lengthCell,installed,fun offset inside=>(prior offset inside).trans (bytes offset inside),run⟩

theorem Observed.unique (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length left right : BitVec 64) (leftObserved : Observed source pointer length left)
    (rightObserved : Observed source pointer length right) : left=right := by
  obtain ⟨leftEntry,leftPost,leftPointer,leftLength,leftInstalled,leftBytes,leftRun⟩ := leftObserved
  obtain ⟨rightEntry,rightPost,rightPointer,rightLength,rightInstalled,rightBytes,rightRun⟩ := rightObserved
  have bytes : BytesAgree leftEntry rightEntry pointer length :=
    fun offset inside=>(leftBytes offset inside).trans (rightBytes offset inside).symm
  have same := body_unique leftEntry rightEntry leftPost rightPost pointer length (.val (.word left)) (.val (.word right))
    leftPointer leftLength rightPointer rightLength bytes leftInstalled rightInstalled leftRun rightRun
  simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using same

/-- The actual original scoped caller supplies an observation and the
genuine readonly continuation. No future successful callee is a premise. -/
theorem scoped_observed (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) (name : String) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some (values pointer length.toNat))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_read_length") arguments continuation)=
      (some (.returned returned),post)) :
    ∃ paid payload inner,1≤paid ∧ paid≤source.clock ∧ Observed source pointer length payload ∧
      evaluateHOLFiniteState (bind {source with clock:=source.clock-paid} name payload) continuation=(some (.returned returned),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length.toNat (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name .one (ofString "rlp_read_length") arguments _ body continuation callee .one args called returned normal
  have typed : shapeOfHOLExact answer=.one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨payload,answerEq⟩ := Input.scalar_word_of_shape answer typed
  subst answer
  have fields := readonly source.code installed (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at fields
  change Input.LocalEffects.erase target=Input.LocalEffects.erase source at fields
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change target.clock≤source.clock-1 at clock
  let paid := source.clock-target.clock
  have remaining : source.clock-paid=target.clock := by dsimp [paid]; omega
  have canonical : Input.CallNormal.continuationEntry source target name (.val (.word payload))=
      bind {source with clock:=source.clock-paid} name payload := by
    have reset := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) fields
    change {target with locals:=source.locals}={source with clock:=target.clock} at reset
    unfold Input.CallNormal.continuationEntry
    rw [reset,remaining]
    rfl
  have observed : Observed source pointer length payload := by
    refine ⟨callEntryStateHOLFinite source callee,target,pointerLocal,?_,installed,?_,bodyRun⟩
    · change callee.lookup (ofString "n")=some (.val (.word length))
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using lengthLocal
    · intro offset inside
      rfl
  rw [canonical] at continuationRun
  exact ⟨paid,payload,inner,by dsimp [paid]; omega,Nat.sub_le _ _,observed,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.Observed.transport
#print axioms InitECandidate.Solver.Rlp.ReadLength.Observed.unique
#print axioms InitECandidate.Solver.Rlp.ReadLength.scoped_observed
