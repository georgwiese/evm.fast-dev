import InitECandidate.Solver.Mpt.WitnessCoreLoopProgram
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) :=
  QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind (QueryBranch.bind
    (QueryBranch.bind (QueryBranch.bind source "top" 0#64) "result" 0#64) "cur_p" pointer) "cur_n" length) "mode" 1#64) "slot" 0#64) "go" 1#64

/-- All seven genuine declarations, including the two actual parameter
reads, execute with no source tick or nonlocal mutation. -/
theorem initial_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    ∃ restoreStack,ProgramPrefix.Executes source initialActions (ready source pointer length) restoreStack := by
  let topSource:=QueryBranch.bind source "top" 0#64
  let resultSource:=QueryBranch.bind topSource "result" 0#64
  let pointerSource:=QueryBranch.bind resultSource "cur_p" pointer
  have currentP : resultSource.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other topSource "result" "p" 0#64 (by decide)).trans ((bind_lookup_other source "top" "p" 0#64 (by decide)).trans pCell)
  have currentN : pointerSource.locals.lookup (ofString "n")=some (.val (.word length)) :=
    (bind_lookup_other resultSource "cur_p" "n" pointer (by decide)).trans ((bind_lookup_other topSource "result" "n" 0#64 (by decide)).trans
      ((bind_lookup_other source "top" "n" 0#64 (by decide)).trans nCell))
  have pRead : eval resultSource (localVar "p")=some (.val (.word pointer)) := by simp [eval,localVar,evalHOLExact,toExact,currentP]
  have nRead : eval pointerSource (localVar "n")=some (.val (.word length)) := by simp [eval,localVar,evalHOLExact,toExact,currentN]
  exact ⟨_,.declare 0#64 rfl (.declare 0#64 rfl (.declare pointer pRead (.declare length nRead
    (.declare 1#64 rfl (.declare 0#64 rfl (.declare 1#64 rfl (.done _)))))))⟩

theorem ready_erase (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) :
    Input.LocalEffects.erase (ready source pointer length)=Input.LocalEffects.erase source := rfl

theorem ready_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) :
    (ready source pointer length).clock=source.clock := rfl

theorem ready_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) :
    (ready source pointer length).locals.lookup (ofString "top")=some (.val (.word 0#64)) ∧
    (ready source pointer length).locals.lookup (ofString "result")=some (.val (.word 0#64)) ∧
    (ready source pointer length).locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
    (ready source pointer length).locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
    (ready source pointer length).locals.lookup (ofString "mode")=some (.val (.word 1#64)) ∧
    (ready source pointer length).locals.lookup (ofString "slot")=some (.val (.word 0#64)) ∧
    (ready source pointer length).locals.lookup (ofString "go")=some (.val (.word 1#64)) := by
  have distinct : ([ofString "go",ofString "slot",ofString "mode",ofString "cur_n",ofString "cur_p",ofString "result",ofString "top"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true,List.nodup_nil] at distinct
  simp_all [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem ready_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (name : MlS)
    (other : name∉[ofString "go",ofString "slot",ofString "mode",ofString "cur_n",ofString "cur_p",ofString "result",ofString "top"]) :
    (ready source pointer length).locals.lookup name=source.locals.lookup name := by
  simp only [List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true] at other
  simp_all [ready,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm]

/-- Reach the literal loop/return suffix from the same actual core-body
execution, retaining all lexical restorations and its exact final clock. -/
theorem initial_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    ∃ restoreStack inner,ProgramPrefix.Executes source initialActions (ready source pointer length) restoreStack ∧
      evaluateHOLFiniteState (ready source pointer length) (.seq (.while condition loopBody) footer)=(outcome,inner) ∧
      post=restoreStack inner ∧ post.clock=inner.clock := by
  obtain ⟨restoreStack,setup⟩ := initial_executes source pointer length pCell nCell
  have actual:=ProgramPrefix.execute setup (.seq (.while condition loopBody) footer)
  rw [header_shape,actual] at run
  let inner:=(evaluateHOLFiniteState (ready source pointer length) (.seq (.while condition loopBody) footer)).2
  have firstEq:=congrArg Prod.fst run
  have lastEq:=congrArg Prod.snd run
  have continued : evaluateHOLFiniteState (ready source pointer length) (.seq (.while condition loopBody) footer)=(outcome,inner) := Prod.ext firstEq rfl
  have endpoint : post=restoreStack inner := lastEq.symm
  have frame:=ProgramPrefix.restoration_frame setup inner
  have clock:=congrArg PanSemStateFiniteExact.clock frame
  change (restoreStack inner).clock=inner.clock at clock
  exact ⟨restoreStack,inner,setup,continued,endpoint,by rw [endpoint]; exact clock⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.initial_executes
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ready_erase
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ready_clock
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ready_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ready_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.initial_trace
