import InitECandidate.Solver.Input.CurrentStartup.HostPrefix
import InitECandidate.Solver.WitnessRadix.AllocationChecked
import InitECandidate.Solver.WitnessRadix.AllocationEnvironment

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The heap facts needed by input_blob, without claiming a startup size. -/
def HeapState (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ pointer : BitVec 64, state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
    pointer.toNat ≤ 2952790016 ∧ pointer.toNat % 8 = 0

theorem allocation_entry (code) (installed : OriginalCode.Installed code) :
    code.lookup (Code.name .alloc) = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one) := by
  simpa only [Code.formals, Code.body, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_alloc, WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body,
    shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using Code.installed code installed .alloc

theorem trap_entry (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "trap_with") = some (Trap.formals, Trap.body, .one) := by
  simpa only [Code.name, Code.formals, Code.body, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_trap_with, Trap.formals, Trap.body,
    shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using Code.installed code installed .trap_with

/-- Any real completed scalar allocation action supplies the bounded aligned
next cursor, even without an invariant on its incoming heap cell. -/
theorem allocation_reached {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (amount : BitVec 64) (installed : OriginalCode.Installed source.code)
    (reached : CallPrefix.Reaches source (.scoped name .one (Code.name .alloc) [.const amount]) target) : HeapState target := by
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
    obtain ⟨pointer, valueEq, heap, bound, aligned⟩ := WitnessRadix.PersistentAlloc.reached_cursor
      (callEntryStateHOLFinite source expectedCallee) post amount amountLocal
      (trap_entry source.code installed) returned run
    exact ⟨_, heap, bound, aligned⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.allocation_entry
#print axioms InitECandidate.Solver.Input.CurrentStartup.trap_entry
#print axioms InitECandidate.Solver.Input.CurrentStartup.allocation_reached
