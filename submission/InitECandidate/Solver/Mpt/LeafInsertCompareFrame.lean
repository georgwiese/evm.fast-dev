import InitECandidate.Solver.Mpt.LeafInsertMatching
import InitECandidate.Solver.Mpt.LeafInsertDispatch
import InitECandidate.Solver.MutableTable.MemeqAnyCall
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem replace_no_fallthrough : Input.NoFallthrough replaceBody := by
  rw [replace_shape 0#64 0#64]
  simp only [FieldStores.program,fields]
  apply Input.NoFallthrough.sequence
  apply Input.NoFallthrough.sequence
  exact Input.NoFallthrough.returned _

/-- A comparison that continues has skipped the replacement completely. -/
theorem compare_guard_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (normal : evaluateHOLFiniteState source compareGuard=(none,target)) : target=source := by
  rw [compare_guard_shape,evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) (.cmp .notEqual (localVar "eq") (.const 0#64))=read at normal
  cases read with
  | none=>cases normal
  | some read=>
    cases read with
    | rStruct fields=>cases normal
    | nStruct name fields=>cases normal
    | val payload=>
      cases payload with
      | word word=>
        by_cases zero : word=0
        · have skipped : evaluateHOLFiniteState source .skip=(none,target):=by simpa only [if_pos zero] using normal
          exact (congrArg Prod.snd ((evaluateHOLFiniteState_skip source).symm.trans skipped)).symm
        · have replaced : evaluateHOLFiniteState source replaceBody=(none,target):=by simpa only [if_neg zero] using normal
          exact (replace_no_fallthrough source (congrArg Prod.fst replaced)).elim

/-- The genuine falling-through memeq scope preserves every nonlocal
field. Its real comparison return is consumed by the original guard. -/
theorem compare_scope_none_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (left size right : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (sizeCell : source.locals.lookup (ofString "el")=some (.val (.word size)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (normal : evaluateHOLFiniteState source compareScope=(none,target)) :
    Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) compareArguments=
      some (MutableTable.MemeqByteRuntime.values left right size.toNat):=by
    simp [compareArguments,MutableTable.MemeqByteRuntime.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,sizeCell,rightCell]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup left right size.toNat
    (MutableTable.MemeqAny.original_code source.code installed)
  rw [dispatch_shapes.2.2.2.2.1] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source target "eq" .one (ofString "memeq") compareArguments _
    Memeq32.body compareGuard callee .one args called normal
  have frame:=(MutableTable.MemeqAny.readonly source.code) (callEntryStateHOLFinite source callee) rfl
  rw [run] at frame
  have innerEq:=compare_guard_none (Input.CallNormal.continuationEntry source child "eq" returned) inner continued
  rw [endpoint,innerEq]
  exact frame

theorem length_choice_none_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (left size right length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (sizeCell : source.locals.lookup (ofString "el")=some (.val (.word size)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (normal : evaluateHOLFiniteState source lengthChoice=(none,target)) :
    Input.LocalEffects.erase target=Input.LocalEffects.erase source := by
  by_cases same : size=length
  · have read : eval source lengthTest=some (.val (.word 1#64)):=by
      simp [eval,lengthTest,evalHOLExact,toExact,localVar,sizeCell,lengthCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at read
    rw [dispatch_shapes.2.2.2.1,evaluateHOLFiniteState_ite,read] at normal
    exact compare_scope_none_frame source target left size right installed leftCell sizeCell rightCell normal
  · have read : eval source lengthTest=some (.val (.word 0#64)):=by
      simp [eval,lengthTest,evalHOLExact,toExact,localVar,sizeCell,lengthCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at read
    rw [dispatch_shapes.2.2.2.1,evaluateHOLFiniteState_ite,read] at normal
    have skipped : evaluateHOLFiniteState source .skip=(none,target):=normal
    have targetEq : target=source:=(congrArg Prod.snd ((evaluateHOLFiniteState_skip source).symm.trans skipped)).symm
    rw [targetEq]

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.replace_no_fallthrough
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.compare_guard_none
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.compare_scope_none_frame
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.length_choice_none_frame
