import InitECandidate.Solver.Input.UDivMod.Built
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordPairConstCost

namespace InitECandidate.Solver.Input.UDivMod
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Nonzero division covers every clock, including an insufficient loop
clock. Its actual64-round software loop supplies the bound. -/
theorem nonzero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (nonzero : b≠0#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤64 := by
  by_cases enough : 64≤source.clock
  · obtain ⟨target,q,r,paid,bound,run,clock,frame,arithmetic⟩:=body_execute_nonzero source a b aLocal bLocal nonzero enough
    rw [run,clock]
    omega
  · omega

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "udivmod")=some (formals,body,returnShape) := by
  have checked:=OriginalCode.indexed code installed 28 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_udivmod) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,returnShape,
    Guest.Software.guestFn_udivmod,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

namespace Divide

def body : ProgHOL 64 := match Guest.Software.guestFn_udiv with | .function fn=>progToHOL fn.body | _=>.skip
def tail : ProgHOL 64 := .return (.rfield 0 (localVar "qr"))

theorem shape : body=.decCall (ofString "qr") returnShape (ofString "udivmod") [localVar "a",localVar "b"] tail := by
  simp only [body,tail,returnShape,Guest.Software.guestFn_udiv,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "udiv")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 29 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_udiv) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_udiv,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Actual scalar division, including its scoped udivmod ABI, needs at
most65 source ticks for every nonzero divisor. -/
theorem nonzero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (aLocal : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (bLocal : source.locals.lookup (ofString "b")=some (.val (.word b))) (nonzero : b≠0#64)
    (code : source.code.lookup (ofString "udivmod")=some (formals,UDivMod.body,returnShape)) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤65 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "a",localVar "b"]=some [.val (.word a),.val (.word b)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,aLocal,bLocal]
  obtain ⟨callee,called,aCell,bCell⟩:=word_pair_environment source.code.lookup (ofString "udivmod") (ofString "a") (ofString "b") UDivMod.body returnShape a b (by decide) code
  rw [shape]
  exact ClockCost.scoped_current source (ofString "qr") returnShape (ofString "udivmod") [localVar "a",localVar "b"] _ UDivMod.body tail callee returnShape 64 0 args called
    (UDivMod.nonzero_cost (callEntryStateHOLFinite source callee) a b aCell bCell nonzero)
    (ClockCost.returned source.code _)

end Divide
end InitECandidate.Solver.Input.UDivMod

#print axioms InitECandidate.Solver.Input.UDivMod.nonzero_cost
#print axioms InitECandidate.Solver.Input.UDivMod.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.Divide.original_code
#print axioms InitECandidate.Solver.Input.UDivMod.Divide.nonzero_cost
