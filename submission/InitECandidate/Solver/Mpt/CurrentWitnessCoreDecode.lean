import InitECandidate.Solver.Mpt.CurrentWitnessDecodeStep
import InitECandidate.Solver.Mpt.WitnessCoreTerminal
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.ScalarWordShape
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.WitnessCore
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem after_decode_zero_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (second : ValueHOL 64)
    (cell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word 0#64),second])) :
    evaluateHOLFiniteState source afterDecode=evaluateHOLFiniteState source decodeTerminal := by
  rw [after_decode_shape]
  simp [evaluateHOLFiniteState_ite,decodeField,localVar,evalHOLExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem after_decode_zero_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (second : ValueHOL 64)
    (cell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word 0#64),second])) :
    source.clock-(evaluateHOLFiniteState source afterDecode).2.clock≤0 := by
  rw [after_decode_zero_choice source second cell]
  have price : ClockCost.Bound source.code decodeTerminal 0 := by
    rw [terminal_shape]
    exact ClockCost.sequence _ _ _ 0 0 (ClockCost.assign _ _ _) (ClockCost.assign _ _ _)
  exact price source rfl

theorem current_decode_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
  simp [decodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,pointerCell,lengthCell]

theorem current_decode_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length : BitVec 64)
    (installed : OriginalCode.Installed source.code) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "_decode_step") [.val (.word db),.val (.word pointer),.val (.word length)]=
      some (WitnessStep.body .decode,callee,.comb [.one,.one]) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word length)) :=
  word_triple_environment source.code.lookup (ofString "_decode_step") (ofString "db") (ofString "p") (ofString "n")
    (WitnessStep.body .decode) (.comb [.one,.one]) db pointer length (by decide) (by decide) (by decide)
    (WitnessStep.original_code .decode source.code installed)

/-- The actual caller can only enter its terminal, zero-source-tick tail.
Its callee's successful return, rather than an assumed branch, supplies this. -/
theorem current_decode_branch_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source decodeBranch).2.clock≤length.toNat/4+195*length.toNat+285 := by
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=current_decode_environment source db pointer length arena.code
  rw [decode_shape]
  have price:=ClockCost.scoped_reached_current source "d" (.comb [.one,.one]) (ofString "_decode_step") decodeArguments _
    (WitnessStep.body .decode) afterDecode callee (.comb [.one,.one]) (length.toNat/4+195*length.toNat+284) 0
    (current_decode_arguments source db pointer length dbCell pointerCell lengthCell) called
    (WitnessDecode.current_step_price (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl))
    (by
      intro target value normal checked
      obtain ⟨second,valueEq⟩:=WitnessDecode.current_step_zero (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl) target value normal
      rw [valueEq]
      exact after_decode_zero_price (CallNormal.continuationEntry source target "d" _) second (CallNormal.continuation_lookup_same _ _ _ _))
  exact Nat.le_trans price (by omega)

/-- Normal continuation of the real decode caller sets mode to zero,
keeps its empty stack, and keeps go enabled for the final loop iteration. -/
theorem current_decode_branch_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap oldResult oldMode : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word 0#64)))
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word 1#64)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    post.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
      post.locals.lookup (ofString "top")=some (.val (.word 0#64)) ∧ post.locals.lookup (ofString "go")=some (.val (.word 1#64)) := by
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=current_decode_environment source db pointer length arena.code
  rw [decode_shape] at normal
  obtain ⟨positive,target,value,inner,bodyRun,checked,continued,restored⟩:=CallNormal.scoped_none source post "d" (.comb [.one,.one])
    (ofString "_decode_step") decodeArguments _ (WitnessStep.body .decode) afterDecode callee (.comb [.one,.one])
    (current_decode_arguments source db pointer length dbCell pointerCell lengthCell) called normal
  obtain ⟨second,rfl⟩:=WitnessDecode.current_step_zero (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl) target value bodyRun
  have shape:=((shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1)
  simp only [shapeOfHOLExact,List.map_cons,List.map_nil] at shape
  have secondShape:= (List.cons.inj (List.cons.inj (ShapeHOL.comb.inj shape)).2).1
  obtain ⟨node,rfl⟩:=scalar_word_of_shape second secondShape
  let ready:=CallNormal.continuationEntry source target "d" (.rStruct [.val (.word 0#64),.val (.word node)])
  have dCell : ready.locals.lookup (ofString "d")=some (.rStruct [.val (.word 0#64),.val (.word node)]):=CallNormal.continuation_lookup_same _ _ _ _
  have currentResult : ready.locals.lookup (ofString "result")=some (.val (.word oldResult)) :=
    (CallNormal.continuation_lookup_other source target "d" "result" _ (by decide)).trans resultCell
  have currentMode : ready.locals.lookup (ofString "mode")=some (.val (.word oldMode)) :=
    (CallNormal.continuation_lookup_other source target "d" "mode" _ (by decide)).trans modeCell
  rw [after_decode_zero_choice ready (.val (.word node)) dCell,terminal_execute ready node oldResult oldMode dCell currentResult currentMode] at continued
  have middleEq : inner=delivered ready node := (congrArg Prod.snd continued).symm
  have other (key : String) (notD : ofString "d"≠ofString key) (notMode : ofString "mode"≠ofString key)
      (notResult : ofString "result"≠ofString key) : post.locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
    rw [restored,middleEq]
    exact (restore_lookup_other source _ "d" key (Ne.symm notD)).trans
      ((bind_lookup_other _ "mode" key 0#64 notMode).trans
        ((bind_lookup_other ready "result" key node notResult).trans (CallNormal.continuation_lookup_other source target "d" key _ notD)))
  refine ⟨?_,(other "top" (by decide) (by decide) (by decide)).trans topCell,(other "go" (by decide) (by decide) (by decide)).trans goCell⟩
  rw [restored,middleEq,restore_lookup_other source _ "d" "mode" (by decide)]
  exact (delivered_fields ready node).2.1

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_decode_branch_price
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_decode_branch_none
