import InitECandidate.Solver.Arenas.Marks
import InitECandidate.Solver.Input.QuietClockEffects
import InitECandidate.Solver.Input.ClockCostCall
import InitECandidate.Solver.Arenas.Cost

namespace InitECandidate.Solver.Arenas.Scratch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def releaseBody : ProgHOL 64 := match Guest.guestFn_scratch_release with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "m",.one)]
def released (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64) :=
  {source with globals:=source.globals.update (ofString "scratch_ptr",.val (.word mark))}

set_option maxRecDepth 100000 in
theorem mark_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "scratch_mark")=some ([],markBody .down,.one) := by
  have checked := Input.OriginalCode.indexed code installed 9 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_scratch_mark) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,markBody,
    Guest.guestFn_scratch_mark,shapeToHOL,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem release_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "scratch_release")=some (formals,releaseBody,.one) := by
  have checked := Input.OriginalCode.indexed code installed 10 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_scratch_release) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,releaseBody,formals,
    Guest.guestFn_scratch_release,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem release_shape : releaseBody=.seq (.assign .global (ofString "scratch_ptr") (localVar "m")) (.return (.const 0#64)) := by
  simp only [releaseBody,Guest.guestFn_scratch_release,progToHOL,expToHOL,localVar]

theorem release_price (code) : Input.ClockCost.Bound code releaseBody 0 := by
  rw [release_shape]
  exact Input.ClockCost.sequence code _ _ 0 0
    (Input.ClockCost.of_quiet code _ (Input.QuietClock.assign_kind code .global _ _))
    (Input.ClockCost.returned code _)

theorem release_call_price (code) (installed : Input.OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (some (none,none)) (ofString "scratch_release") arguments) 1 :=
  Input.ClockCost.call_body code (some none) (ofString "scratch_release") arguments formals releaseBody .one 0 (release_code code installed) (release_price code)

theorem release_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (m : source.locals.lookup (ofString "m")=some (.val (.word mark)))
    (cursor : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word old))) :
    evaluateHOLFiniteState source releaseBody=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (released source mark)) := by
  have assignRun : evaluateHOLFiniteState source (.assign .global (ofString "scratch_ptr") (localVar "m"))=(none,released source mark) := by
    rw [evaluateHOLFiniteState_assign]
    simp [localVar,evalHOLExact,toExact,m,isValidValueHOLFinite,lookupKvarHOLFinite,cursor,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,setGlobalHOLFinite,released]
  rw [release_shape,WitnessRadix.StateSteps.next_sequence source (released source mark) _ _ assignRun (Nat.le_refl _)]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

end InitECandidate.Solver.Arenas.Scratch

#print axioms InitECandidate.Solver.Arenas.Scratch.mark_code
#print axioms InitECandidate.Solver.Arenas.Scratch.release_code
#print axioms InitECandidate.Solver.Arenas.Scratch.release_shape
#print axioms InitECandidate.Solver.Arenas.Scratch.release_price
#print axioms InitECandidate.Solver.Arenas.Scratch.release_call_price
#print axioms InitECandidate.Solver.Arenas.Scratch.release_execute
