import InitECandidate.Solver.Input.ByteWriterMemory
import InitECandidate.Solver.Input.CopyAwaySubrange
import InitECandidate.Solver.Input.MemoryConstantLoop
import InitECandidate.Solver.Input.ShaGlobals

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def finishAddress : ExpHOL 64 := .op .add [localVar "out",.panop .mul [localVar "i",.const 4#64]]
def finishValue : ExpHOL 64 := .load .one (.op .add [localVar "stp",.panop .mul [localVar "i",.const 8#64]])

theorem finish_arguments_shape : finishArguments=[finishAddress,finishValue] := by
  simp only [finishArguments,finishStep,finishLoop,finishBody,BuildProgram.loops,Guest.guestFn_sha256_finish,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some,Option.map_none,finishAddress,finishValue,localVar]

theorem finish_other (key : MlS) (different : key≠ofString "i") : LocalPrefix key finishStep := by
  rw [step_shape]
  exact .seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ different)

theorem finish_advance : CounterFlow.Advances (ofString "i") 1 finishStep := by
  rw [step_shape]
  exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.call none _ _ (by intro name impossible; cases impossible))) (CounterFlow.increment _)

theorem finish_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index : Nat)
    (installed : OriginalCode.Installed source.code) (active : index<8)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away pointer query 32) (run : evaluateHOLFiniteState source finishStep=(none,post)) : post.memory query=source.memory query := by
  rw [step_shape,finish_arguments_shape] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_none source post _ increment run
  have read : eval source finishAddress=some (.val (.word (pointer+BitVec.ofNat 64 (4*index)))) := by
    simp [eval,finishAddress,evalHOLExact,evalListHOLExact,toExact,localVar,output,position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  have called := MemoryWordCalls.be32_call_memory source middle finishAddress finishValue (pointer+BitVec.ofNat 64 (4*index)) query installed read (CopyGeneral.Away.subrange pointer query 32 (4*index) 4 away (by omega)) normal
  have assigned := MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=(none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans called

theorem finish_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (away : CopyGeneral.Away pointer query 32)
    (run : evaluateHOLFiniteState source (.while (.cmp .less (localVar "i") (.const 8#64)) finishStep)=(none,post)) : post.memory query=source.memory query := by
  have summary := MemoryAt.constant_loop_normal source.code (ofString "i") (ofString "marker") finishStep 8 query (by decide)
    (finish_other (ofString "marker") (by decide)).summary_full finish_advance
    (fun current=>current.locals.lookup (ofString "out")=some (.val (.word pointer))) (by intro current actual; exact actual)
    (by intro current codeEq currentOutput index active currentPosition target bodyRun
        have localFrame := (finish_other (ofString "out") (by decide)).summary_full current
        unfold LocalSummary at localFrame
        rw [bodyRun] at localFrame
        exact ⟨(localFrame.1 rfl).trans currentOutput,finish_step_memory current target pointer query index (codeEq.symm ▸ installed) active currentOutput currentPosition away bodyRun⟩)
    source post 0 rfl output (by decide) position run
  exact summary.2.2

/-- The actual original eight-word SHA finish writes only output32; real
normal BE32 calls derive their value reads from that same execution. -/
theorem finish_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (output : source.locals.lookup (ofString "out")=some (.val (.word pointer))) (away : CopyGeneral.Away pointer query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source finishBody=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [finish_shape] at run
  refine MemoryAt.declaration_returned source post "i" (.const 0#64) 0#64 query _ value rfl ?_ run
  intro inner remaining
  let entry := bind source "i" 0#64
  have nextOutput : entry.locals.lookup (ofString "out")=some (.val (.word pointer)) := (bind_lookup_other source "i" "out" 0#64 (by decide)).trans output
  have safe : LocalPrefix (ofString "out") (.while (.cmp .less (localVar "i") (.const 8#64)) finishStep) := .loop _ (finish_other (ofString "out") (by decide))
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned entry inner _ (.return (.const 0#64)) value (safe.summary_full entry).2.1 remaining
  have frame := finish_loop_memory entry middle pointer query installed nextOutput (bind_lookup_same _ _ _) away normal
  have finalFrame := MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at finalFrame
  exact finalFrame.trans frame

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_arguments_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_other
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_advance
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_step_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_loop_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_memory
