import InitECandidate.Solver.Input.RlpWrite.U256MinCall

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def markBody : ProgHOL 64 := match Guest.guestFn_heap_mark with | .function fn=>progToHOL fn.body | _=>.skip
def releaseBody : ProgHOL 64 := match Guest.guestFn_heap_release with | .function fn=>progToHOL fn.body | _=>.skip
def releaseFormals : List (MlS×ShapeHOL) := [(ofString "m",.one)]
def heapVar : ExpHOL 64 := .var .global (ofString "heap_ptr")
def releasePost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word mark))}

theorem mark_shape : markBody=.return heapVar := by
  simp only [markBody,Guest.guestFn_heap_mark,progToHOL,expToHOL,heapVar]

theorem release_shape : releaseBody=.seq (.assign .global (ofString "heap_ptr") (localVar "m")) (.return (.const 0#64)) := by
  simp only [releaseBody,Guest.guestFn_heap_release,progToHOL,expToHOL,localVar]

theorem mark_call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64) (name : String) (continuation : ProgHOL 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)))
    (code : source.code.lookup (ofString "heap_mark")=some ([],markBody,.one)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "heap_mark") [] continuation)=
      (let output:=evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name mark) continuation
      (output.1,restore source name output.2)) := by
  classical
  have raw : lookupCodeHOLExact source.code.lookup (ofString "heap_mark") []=some (markBody,(fun _=>none),.one) := by
    simp [lookupCodeHOLExact,code]
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "heap_mark") [] markBody (fun _=>none) .one raw
  let entry:=callEntryStateHOLFinite source callee
  have heapEntry : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)):=heap
  have bodyRun : evaluateHOLFiniteState entry markBody=(some (.returned (.val (.word mark))),emptyLocalsHOLFinite entry) := by
    rw [mark_shape]
    simp [evaluateHOLFiniteState_return,heapVar,evalHOLExact,toExact,heapEntry,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have frame : emptyLocalsHOLFinite (emptyLocalsHOLFinite entry)=emptyLocalsHOLFinite {source with clock:=source.clock-1-0}:=rfl
  have actual:=CallNormal.pure_return_execute source (emptyLocalsHOLFinite entry) name (ofString "heap_mark") [] [] markBody continuation callee mark 0 rfl called enough bodyRun frame
  simpa only [Nat.sub_zero] using actual

theorem release_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (m : source.locals.lookup (ofString "m")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old))) :
    evaluateHOLFiniteState source releaseBody=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite (releasePost source mark)) := by
  classical
  have assignRun : evaluateHOLFiniteState source (.assign .global (ofString "heap_ptr") (localVar "m"))=(none,releasePost source mark) := by
    rw [evaluateHOLFiniteState_assign]
    simp [localVar,evalHOLExact,toExact,m,isValidValueHOLFinite,lookupKvarHOLFinite,heap,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,setGlobalHOLFinite,releasePost]
  rw [release_shape,WitnessRadix.StateSteps.next_sequence source (releasePost source mark) _ _ assignRun (Nat.le_refl _)]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]

theorem release_call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word mark)])
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (code : source.code.lookup (ofString "heap_release")=some (releaseFormals,releaseBody,.one)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") expressions)=
      (none,releasePost {source with clock:=source.clock-1} mark) := by
  classical
  obtain ⟨callee,called,m⟩:=CallNormal.unary_environment source.code.lookup (ofString "heap_release") "m" releaseBody mark code
  let entry:=callEntryStateHOLFinite source callee
  have bodyRun:=release_execute entry mark old m heap
  have actual:=evaluateHOLFiniteState_call_return_caller_locals source none (ofString "heap_release") expressions [.val (.word mark)] releaseBody callee .one
    (.val (.word 0#64)) (emptyLocalsHOLFinite (releasePost entry mark)) args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  exact actual

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.mark_call_execute
#print axioms InitECandidate.Solver.Input.HeapScope.release_execute
#print axioms InitECandidate.Solver.Input.HeapScope.release_call_execute
