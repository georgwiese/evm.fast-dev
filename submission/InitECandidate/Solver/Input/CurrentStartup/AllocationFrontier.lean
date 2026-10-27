import InitECandidate.Solver.Input.CurrentStartup.AllocationCursor
import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.WitnessRadix.AllocationNormal

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real scoped allocation returns the current frontier, derives room,
and produces its exact caller state. No future room or success is assumed. -/
theorem allocation_frontier {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (amount : BitVec 64) (lower : Nat) (installed : OriginalCode.Installed source.code)
    (heap : NormalHeapEffects.AtLeast lower source)
    (reached : CallPrefix.Reaches source (.scoped name .one (Code.name .alloc) [.const amount]) target) :
    ∃ pointer : BitVec 64, source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
      lower ≤ pointer.toNat ∧ pointer.toNat % 8 = 0 ∧ pointer.toNat + amount.toNat ≤ 2952790016 ∧
      target = setVarHOLFinite name (.val (.word pointer))
        (WitnessRadix.PersistentAlloc.post {source with clock := source.clock - 1} pointer amount) := by
  obtain ⟨pointer, heapCell, low, high, aligned⟩ := heap
  obtain ⟨expectedCallee, expectedLookup, amountLocal⟩ := WitnessRadix.PersistentAlloc.environment
    source.code.lookup amount (allocation_entry source.code installed)
  cases reached with
  | «scoped» _ _ _ _ values body callee shape returned post args called funded run checked =>
    have argsEq : values = WitnessRadix.PersistentAlloc.values amount := by
      have canonical : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
          [.const amount] = some (WitnessRadix.PersistentAlloc.values amount) := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, WitnessRadix.PersistentAlloc.values]
      exact Option.some.inj (args.symm.trans canonical)
    subst values
    have same := Option.some.inj (called.symm.trans expectedLookup)
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj same
    obtain ⟨valueEq, room, frame⟩ := WitnessRadix.PersistentAlloc.post_of_normal
      (callEntryStateHOLFinite source expectedCallee) post pointer amount amountLocal heapCell high
      (trap_entry source.code installed) returned run
    subst returned
    refine ⟨pointer, heapCell, low, aligned, room, ?_⟩
    have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      setVarHOLFinite name (.val (.word pointer)) {state with locals := source.locals}) frame
    exact actual

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.allocation_frontier
