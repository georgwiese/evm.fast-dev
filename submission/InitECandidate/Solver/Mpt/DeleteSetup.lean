import InitECandidate.Solver.Mpt.DeleteBodyProgram
import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.CallPrefixDeclaration

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def actions : List Input.CallPrefix.Action:=[.declare (ofString "top") .one (.const 0#64),
  .declare (ofString "res") .one (.const 0#64),.declare (ofString "go") .one (.const 1#64)]
def setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  QueryBranch.bind (QueryBranch.bind (QueryBranch.bind source "top" 0#64) "res" 0#64) "go" 1#64

theorem body_setup_shape : body=Input.CallPrefix.program actions afterGo := by
  rw [setup_shapes.1,setup_shapes.2.1,setup_shapes.2.2.1]
  rfl

theorem setup_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (setup source).locals.lookup (ofString "top")=some (.val (.word 0#64)) ∧
      (setup source).locals.lookup (ofString "res")=some (.val (.word 0#64)) ∧
      (setup source).locals.lookup (ofString "go")=some (.val (.word 1#64)) := by
  simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem setup_saved (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS)
    (notTop : ofString "top"≠name) (notResult : ofString "res"≠name) (notGo : ofString "go"≠name) :
    (setup source).locals.lookup name=source.locals.lookup name := by
  simp [setup,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notTop,notResult,notGo]

/-- The actual three original declarations establish top0/res0/go1.
Normal execution supplies its real remaining descent/unwind body and
lexical restoration, rather than a future successful call premise. -/
theorem normal_setup (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ inner,target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧
      evaluateHOLFiniteState (setup source) afterGo=(some (.returned value),inner) := by
  have never : Input.NoReturn.Never (Input.CallPrefix.program actions .skip):=
    Input.NoReturn.declared _ _ _ _ (Input.NoReturn.declared _ _ _ _ (Input.NoReturn.declared _ _ _ _ Input.NoReturn.skip))
  rw [body_setup_shape] at normal
  obtain ⟨current,inner,trace,clock,continued⟩:=Input.CallPrefix.normal_trace source target actions afterGo value never normal
  have first:=trace.declare_next (.val (.word 0#64)) rfl
  have second:=first.declare_next (.val (.word 0#64)) rfl
  have last:=second.declare_next (.val (.word 1#64)) rfl
  have same : current=setup source:=by cases last; rfl
  have frame:=trace.erase afterGo
  rw [normal,continued] at frame
  exact ⟨inner,clock,frame,by simpa only [same] using continued⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.body_setup_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.setup_locals
#print axioms InitECandidate.Solver.Mpt.DeleteBody.setup_saved
#print axioms InitECandidate.Solver.Mpt.DeleteBody.normal_setup
