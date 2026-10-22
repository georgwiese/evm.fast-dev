import InitECandidate.Solver.Mpt.InsertEmptyChoice

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def firstDispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory):=
  dispatchEntry (decClockHOLFinite (setup source))

/-- An actual insertion into an empty root reaches the original assigned
node_new_leaf call. The real helper return and all later remainders are
exposed, rather than supplied as a future leaf-constructor assumption. -/
theorem empty_leaf_entry (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ inner last iterationPost leafPost iterationInner,
      target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧ 1≤source.clock ∧
      evaluateHOLFiniteState (decClockHOLFinite (setup source)) loopBody=(none,iterationPost) ∧
      evaluateHOLFiniteState (firstDispatch source) leafCall=(none,leafPost) ∧
      evaluateHOLFiniteState leafPost afterChoice=(none,iterationInner) ∧
      iterationPost.clock=iterationInner.clock ∧ Input.LocalEffects.erase iterationPost=Input.LocalEffects.erase iterationInner ∧
      evaluateHOLFiniteState iterationPost (.while test loopBody)=(none,last) ∧
      evaluateHOLFiniteState last (.return (localVar "result"))=(some (.returned value),inner) := by
  obtain ⟨inner,last,iterationPost,clock,frame,funded,bodyRun,forward,tailRun,returnRun⟩:=first_iteration source target value normal
  have firstGo : (decClockHOLFinite (setup source)).locals.lookup (ofString "go")=some (.val (.word 1#64)):=
    (setup_locals source).2.2
  have execution:=prefix_execution (decClockHOLFinite (setup source)) 1#64 firstGo
  have originalBodyRun:=bodyRun
  rw [iteration_shape] at bodyRun
  have replay:=execution.project (.seq nodeChoice afterChoice)
  rw [bodyRun] at replay
  let iterationInner:=(evaluateHOLFiniteState (firstDispatch source) (.seq nodeChoice afterChoice)).2
  have resultEq:=congrArg Prod.fst replay
  have remaining : evaluateHOLFiniteState (firstDispatch source) (.seq nodeChoice afterChoice)=(none,iterationInner):=
    Prod.ext resultEq.symm rfl
  have stepClock : iterationPost.clock=iterationInner.clock:=congrArg Prod.snd replay
  have stepFrame:=execution.erase (.seq nodeChoice afterChoice)
  rw [bodyRun] at stepFrame
  change Input.LocalEffects.erase iterationPost=Input.LocalEffects.erase
    (evaluateHOLFiniteState (firstDispatch source) (.seq nodeChoice afterChoice)).2 at stepFrame
  rw [remaining] at stepFrame
  obtain ⟨leafPost,choiceRun,afterRun⟩:=Input.sequence_none (firstDispatch source) iterationInner nodeChoice afterChoice remaining
  have currentNode : (firstDispatch source).locals.lookup (ofString "node")=some (.val (.word 0#64)):=by
    simpa [firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using nodeCell
  rw [empty_choice (firstDispatch source) currentNode] at choiceRun
  exact ⟨inner,last,iterationPost,leafPost,iterationInner,clock,frame,funded,originalBodyRun,choiceRun,afterRun,stepClock,stepFrame,tailRun,returnRun⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_leaf_entry
