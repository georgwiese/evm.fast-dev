import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.CommonPrefixCall
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original extension comparison computes its prefix against the
actual remaining key, with no assumption of a future equal-byte result. -/
theorem extension_prefix_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (segment oldLength key level length : BitVec 64) (bounded : length.toNat≤64) (before : level.toNat≤length.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (oldLengthCell : source.locals.lookup (ofString "sl")=some (.val (.word oldLength)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (normal : evaluateHOLFiniteState source extensionPrefixScope=(none,target)) :
    ∃ ready inner,∃ prefixLength : BitVec 64,prefixLength.toNat≤min oldLength.toNat (length.toNat-level.toNat) ∧
      ready.locals.lookup (ofString "pl")=some (.val (.word prefixLength)) ∧
      ready.locals=source.locals.update (ofString "pl",.val (.word prefixLength)) ∧
      Input.LocalEffects.erase ready=Input.LocalEffects.erase source ∧ source.clock-ready.clock≤length.toNat-level.toNat+2 ∧
      evaluateHOLFiniteState ready extensionPrefixChoice=(none,inner) ∧ target=restore source "pl" inner := by
  have subtraction : (length-level).toNat=length.toNat-level.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have small : min oldLength.toNat (length-level).toNat≤64:=by rw [subtraction]; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) prefixArguments=
      some (CommonPrefix.values segment oldLength (key+level) (length-level)):=by
    simp [prefixArguments,queryPointer,queryLength,CommonPrefix.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
      segmentCell,oldLengthCell,keyCell,levelCell,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨callee,called,aCell,alCell,bCell,blCell⟩:=CommonPrefix.environment source.code.lookup segment oldLength (key+level) (length-level) (CommonPrefix.original_code source.code installed)
  rw [extension_shapes.2.2.1] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source target "pl" .one (ofString "common_prefix_length") prefixArguments _
    CommonPrefix.body extensionPrefixChoice callee .one args called normal
  obtain ⟨prefixLength,answer,bound,cost,frame⟩:=CommonPrefix.body_normal (callEntryStateHOLFinite source callee) child oldLength (length-level) small installed alCell blCell returned run
  let ready:=Input.CallNormal.continuationEntry source child "pl" returned
  have price : source.clock-ready.clock≤length.toNat-level.toNat+2:=by
    change source.clock-1-child.clock≤min oldLength.toNat (length-level).toNat+1 at cost
    change source.clock-child.clock≤length.toNat-level.toNat+2
    rw [subtraction] at cost
    have shorter:=Nat.min_le_right oldLength.toNat (length.toNat-level.toNat)
    omega
  rw [subtraction] at bound
  refine ⟨ready,inner,prefixLength,bound,?_,?_,frame,price,continued,endpoint⟩
  · simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · simp [ready,Input.CallNormal.continuationEntry,answer,setVarHOLFinite]

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_prefix_entry
