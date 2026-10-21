import InitECandidate.Solver.Input.CoreDecodeCallNormal
import InitECandidate.Solver.Input.CoreDecodeResumeNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete actual original core decode-mode normal iteration. Its real
helper return derives a delivered node/mode0 or a genuine physical
push/mode2 with fresh stage data, complete ownership and actual record
resource decrease. The original d scope is restored exactly. -/
theorem core_decode_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit previous oldResult oldSlot oldMode : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word previous)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputLower : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source Mpt.WitnessCore.decodeBranch=(none,post)) :
    ∃ built returned,
      let ready:=CallNormal.continuationEntry source built "d" returned
      Mpt.WitnessDecode.NormalFrame source post heap cursor limit ∧
      Mpt.WitnessDecode.NormalResult post db pointer length heap cursor limit returned ∧
      ((∃ node,returned=.rStruct [.val (.word 0#64),.val (.word node)] ∧ post=restore source "d" (Mpt.WitnessCore.delivered ready node)) ∨
        ∃ data : Mpt.WitnessRecord.Description,
          returned=.rStruct [.val (.word 1#64),.val (.word (Mpt.WitnessRecord.pointer cursor))] ∧ data.payload.Fresh ∧
          Mpt.WitnessRecord.View post (Mpt.WitnessRecord.pointer cursor) db data ∧
          post=restore source "d" (Mpt.WitnessCore.pushed ready (Mpt.WitnessRecord.pointer cursor) previous data.payload)) := by
  obtain ⟨built,returned,inner,frame,result,dCell,continued,endpoint⟩:=core_decode_call_normal input source post db pointer length heap cursor limit boundary dbCell pointerCell lengthCell
    heapCell arena before small inputLower below installed normal
  let ready:=CallNormal.continuationEntry source built "d" returned
  have currentTop : ready.locals.lookup (ofString "top")=some (.val (.word previous)):=
    (CallNormal.continuation_lookup_other source built "d" "top" returned (by decide)).trans topCell
  have currentResult : ready.locals.lookup (ofString "result")=some (.val (.word oldResult)):=
    (CallNormal.continuation_lookup_other source built "d" "result" returned (by decide)).trans resultCell
  have currentSlot : ready.locals.lookup (ofString "slot")=some (.val (.word oldSlot)):=
    (CallNormal.continuation_lookup_other source built "d" "slot" returned (by decide)).trans slotCell
  have currentMode : ready.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (CallNormal.continuation_lookup_other source built "d" "mode" returned (by decide)).trans modeCell
  obtain ⟨next,actual,nextFrame,nextResult,shape⟩:=core_decode_resume_normal source ready db pointer length heap cursor limit previous oldResult oldSlot oldMode returned arena frame result dCell
    currentTop currentResult currentSlot currentMode
  have innerEq:=congrArg Prod.snd (continued.symm.trans actual)
  change inner=next at innerEq
  have postEq : post=restore source "d" next:=by rw [endpoint,innerEq]
  have postFrame:=nextFrame.of_erase source post next heap cursor limit (by rw [postEq]; rfl)
  have postResult : Mpt.WitnessDecode.NormalResult post db pointer length heap cursor limit returned:=by
    apply nextResult.of_fields next post db pointer length heap cursor limit returned
    · rw [postEq]; rfl
    · rw [postEq]; rfl
    · rw [postEq]; rfl
  refine ⟨built,returned,postFrame,postResult,?_⟩
  rcases shape with ⟨node,valueEq,nodeEq⟩|⟨data,valueEq,fresh,view,pushedEq⟩
  · exact Or.inl ⟨node,valueEq,by rw [postEq,nodeEq]⟩
  · have finalView : Mpt.WitnessRecord.View post (Mpt.WitnessRecord.pointer cursor) db data:=by
      apply view.of_fields next post _ db data
      · rw [postEq]; rfl
      · rw [postEq]; rfl
    exact Or.inr ⟨data,valueEq,fresh,finalView,by rw [postEq,pushedEq]⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_decode_normal
