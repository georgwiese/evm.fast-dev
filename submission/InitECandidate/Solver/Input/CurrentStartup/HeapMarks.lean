import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.HeapScope
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.CurrentStartup.HeapMarks
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem mark_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (Code.name .heap_mark) = some ([], HeapScope.markBody, .one) := by
  simpa only [Code.formals, Code.body, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_mark,
    HeapScope.markBody, shapeToHOL, List.map_nil] using Code.installed code installed .heap_mark

theorem release_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "heap_release") = some (HeapScope.releaseFormals, HeapScope.releaseBody, .one) := by
  simpa only [Code.name, Code.formals, Code.body, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.Software.guestFn_heap_release,
    HeapScope.releaseBody, HeapScope.releaseFormals, shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .heap_release

def marked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : MlS) (pointer : BitVec 64) :=
  setVarHOLFinite name (.val (.word pointer)) {source with clock := source.clock - 1}

/-- An actual completed snapshot action installs the genuine incoming heap
cursor in its live caller binding, retaining all caller nonlocal state. -/
theorem mark_reached {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (name : MlS) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (reached : CallPrefix.Reaches source (.scoped name .one (Code.name .heap_mark) []) target) :
    target = marked source name pointer := by
  cases reached with
  | «scoped» _ _ _ _ values actualBody callee returnShape returned childTarget args called funded run checked =>
    have bodyEq := GlobalEffects.lookup_body source.code (Code.name .heap_mark) [] HeapScope.markBody .one
      (mark_code source.code installed) values actualBody callee returnShape called
    subst actualBody
    have entryHeap : (callEntryStateHOLFinite source callee).globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := heap
    have actual : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) HeapScope.markBody =
        (some (.returned (.val (.word pointer))), emptyLocalsHOLFinite (callEntryStateHOLFinite source callee)) := by
      rw [HeapScope.mark_shape]
      simp [evaluateHOLFiniteState_return, HeapScope.heapVar, evalHOLExact, toExact, entryHeap,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have valueEq := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst (run.symm.trans actual)))
    have targetEq : childTarget = emptyLocalsHOLFinite (callEntryStateHOLFinite source callee) := congrArg Prod.snd (run.symm.trans actual)
    rw [valueEq, targetEq]
    rfl

/-- The real release restores its checked saved mark. Its caller funding is
derived from the observed call, and the current heap cell from its invariant. -/
theorem release_lower (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code) (initial : NormalHeapEffects.AtLeast lower source)
    (saved : source.locals.lookup (ofString "mark") = some (.val (.word pointer)))
    (low : lower ≤ pointer.toNat) (high : pointer.toNat ≤ 2952790016) (aligned : pointer.toNat % 8 = 0)
    (actual : evaluateHOLFiniteState source (.call (some (none, none)) (Code.name .heap_release)
      [.var .local (ofString "mark")]) = (none, target)) : NormalHeapEffects.AtLeast lower target := by
  obtain ⟨old, heap, oldLow, oldHigh, oldAligned⟩ := initial
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [.var .local (ofString "mark")] = some [.val (.word pointer)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, saved]
  have positive := (CallNormal.ignored_data source target (Code.name .heap_release) _ actual).1
  have expected := HeapScope.release_call_execute source pointer old _ args heap (release_code source.code installed) positive
  have same : target = HeapScope.releasePost {source with clock := source.clock - 1} pointer :=
    congrArg Prod.snd (actual.symm.trans expected)
  refine ⟨pointer, ?_, low, high, aligned⟩
  rw [same]
  simp [HeapScope.releasePost, HolFiniteMapExact.update, FUPDATE]

end InitECandidate.Solver.Input.CurrentStartup.HeapMarks

#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMarks.mark_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMarks.release_code
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMarks.mark_reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMarks.release_lower
