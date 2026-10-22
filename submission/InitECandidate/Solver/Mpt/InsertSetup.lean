import InitECandidate.Solver.Mpt.InsertProgram
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem setup_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (setup source).locals.lookup (ofString "result")=some (.val (.word 0#64)) ∧
      (setup source).locals.lookup (ofString "slot")=some (.val (.word 0#64)) ∧
      (setup source).locals.lookup (ofString "go")=some (.val (.word 1#64)) := by
  simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem setup_saved (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS)
    (notResult : ofString "result"≠name) (notSlot : ofString "slot"≠name) (notGo : ofString "go"≠name) :
    (setup source).locals.lookup name=source.locals.lookup name := by
  simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notResult,notSlot,notGo]

theorem setup_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    eval (setup source) test=some (.val (.word 1#64)) := by
  have go:=(setup_locals source).2.2
  simp [eval,test,localVar,evalHOLExact,toExact,go,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The genuine insertion always enters its original first traversal
iteration. The actual body, subsequent loop and final return are exposed
with the ending metadata, rather than assumed as future successful calls. -/
theorem first_iteration (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ inner last next,target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧
      1≤source.clock ∧ evaluateHOLFiniteState (decClockHOLFinite (setup source)) loopBody=(none,next) ∧
      next.clock≤source.clock-1 ∧ evaluateHOLFiniteState next (.while test loopBody)=(none,last) ∧
      evaluateHOLFiniteState last (.return (localVar "result"))=(some (.returned value),inner) := by
  obtain ⟨inner,clock,frame,continued⟩:=normal_setup source target value normal
  rw [loop_shape] at continued
  have safe : Input.LocalPrefix (ofString "klen") (.while test loopBody):=.loop test loop_body_safe
  obtain ⟨last,loopRun,returnRun⟩:=Input.sequence_returned (setup source) inner (.while test loopBody) (.return (localVar "result")) value
    (fun returned=>(safe.summary_full (setup source)).2.1 returned) continued
  obtain ⟨funded,next,bodyRun,tailRun,forward⟩:=Input.while_none_step (setup source) last (ofString "klen") test loopBody loop_body_safe
    (setup_test source) loopRun
  exact ⟨inner,last,next,clock,frame,funded,bodyRun,forward,tailRun,returnRun⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.setup_locals
#print axioms InitECandidate.Solver.Mpt.Insert.setup_saved
#print axioms InitECandidate.Solver.Mpt.Insert.setup_test
#print axioms InitECandidate.Solver.Mpt.Insert.first_iteration
