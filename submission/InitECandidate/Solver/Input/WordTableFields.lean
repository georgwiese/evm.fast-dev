import InitECandidate.Solver.Input.WordTableInitialization
import InitECandidate.Solver.Input.InitializerMemoryFrame

namespace InitECandidate.Solver.Input.WordTableInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) :
    (template source cursor action words).globals = (InitializerAllocations.template source cursor [action]).globals := rfl

theorem template_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) :
    (template source cursor action words).clock = source.clock := InitializerAllocations.template_clock_value source cursor [action]

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64))
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor action words).globals := by
  rw [template_globals]
  exact InitializerAllocations.template_scalars source cursor [action] scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) (valid : InitializerAllocations.Valid action) :
    (template source cursor action words).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + action.bytes)))) := by
  rw [template_globals]
  have allValid : ∀ current ∈ [action],InitializerAllocations.Valid current := by intro current member; have same := List.mem_singleton.mp member; subst current; exact valid
  simpa only [InitializerAllocations.totalBytes,Nat.add_zero] using InitializerAllocations.template_heap source cursor [action] heap allValid

theorem template_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) :
    (template source cursor action words).globals.lookup (ofString action.name) = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  rw [template_globals]
  exact allocated_binding source cursor action

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : key ≠ ofString action.name) :
    (template source cursor action words).globals.lookup key = source.globals.lookup key := by
  rw [template_globals]
  apply InitializerAllocations.template_other source cursor [action] key heap
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  exact other

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64)) :
    InitializerAllocations.context (template source cursor action words) = InitializerAllocations.context source := by
  unfold template InitializerWords.written
  rw [InitializerAllocations.context_memory,InitializerAllocations.template_context]

/-- The complete physical table effect is confined to the allocated arena. -/
theorem template_window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) (words : List (BitVec 64))
    (arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) action.bytes) (inside : 8 * words.length ≤ action.bytes) :
    Rlp.Slices.Window source (template source cursor action words) (BitVec.ofNat 64 cursor).toNat ((BitVec.ofNat 64 cursor).toNat + action.bytes) := by
  intro query outside
  have frame := InitializerWords.window (InitializerAllocations.template source cursor [action]) (BitVec.ofNat 64 cursor) 0 action.bytes words arena (by simpa only [Nat.zero_add] using inside) query outside
  exact frame.trans (congrArg (fun memory : WordWrites.Memory => memory query) (InitializerAllocations.template_memory source cursor [action]))

end InitECandidate.Solver.Input.WordTableInitialization

#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_globals
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_clock_value
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_heap
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_binding
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_other
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_context
#print axioms InitECandidate.Solver.Input.WordTableInitialization.template_window
