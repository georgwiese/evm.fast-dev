import InitECandidate.Solver.Input.MainForkInitialization

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem valid : ∀ action,action ∈ actions → InitializerAllocations.Valid action := by
  intro action member
  simp only [actions,finalActions,List.mem_cons,List.mem_append,List.mem_map,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | ⟨row,present,rfl⟩ | rfl
  · exact initial_valid.1
  · exact initial_valid.2.1
  · exact address_valid row present
  · exact initial_valid.2.2

theorem total_bytes : InitializerAllocations.totalBytes actions = 592 := by decide_cbv
theorem action_names : actions.map (fun action => action.name) = symbols := by decide_cbv

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := InitializerAllocations.template_clock source cursor actions clock

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := InitializerAllocations.template_context source cursor actions

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 592)))) := by
  have actual := InitializerAllocations.template_heap source cursor actions heap valid
  simpa only [template,total_bytes] using actual

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := InitializerAllocations.template_scalars source cursor actions scalars

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (different : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocations.template_other source cursor actions key notHeap
  intro action member
  apply different action.name
  rw [← action_names]
  exact List.mem_map.mpr ⟨action,member,rfl⟩

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.total_bytes
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.action_names
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.template_other
