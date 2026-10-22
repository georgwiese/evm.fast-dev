import InitECandidate.Solver.Input.OriginalRlpCodes
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def heapMarked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (pointer : BitVec 64):=
  setVarHOLFinite name (.val (.word pointer)) {source with clock:=source.clock-1}

theorem Reaches.heap_mark_target {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (pointer : BitVec 64) (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (reached : Reaches source (.scoped name .one (ofString "heap_mark") []) target) : target=heapMarked source name pointer := by
  cases reached with
  | «scoped» _ _ _ _ values actualBody callee returnShape returned childTarget args called funded run checked=>
    have bodyEq:=GlobalEffects.lookup_body source.code (ofString "heap_mark") [] HeapScope.markBody .one
      (OriginalRlp.heap_mark source.code installed) values actualBody callee returnShape called
    subst actualBody
    have entryHeap : (callEntryStateHOLFinite source callee).globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)):=heap
    have actual : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) HeapScope.markBody=
        (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite (callEntryStateHOLFinite source callee)):=by
      rw [HeapScope.mark_shape]
      simp [evaluateHOLFiniteState_return,HeapScope.heapVar,evalHOLExact,toExact,entryHeap,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have result:=congrArg Prod.fst (run.symm.trans actual)
    have targetEq:=congrArg Prod.snd (run.symm.trans actual)
    have valueEq:=PanSemResultExact.returned.inj (Option.some.inj result)
    change childTarget=emptyLocalsHOLFinite (callEntryStateHOLFinite source callee) at targetEq
    rw [valueEq,targetEq]
    rfl

theorem Execution.heap_mark_next {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (pointer : BitVec 64) (rest : List Action) (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (execution : Execution source (.scoped name .one (ofString "heap_mark") []::rest) target) :
    Execution (heapMarked source name pointer) rest target := by
  obtain ⟨middle,first,next⟩:=execution.head
  rw [first.heap_mark_target name pointer installed heap] at next
  exact next

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.heap_mark_target
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.heap_mark_next
