import InitECandidate.Solver.Input.MainEvmLayout

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := InitializerAllocations.template_clock source cursor actions clock

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := InitializerAllocations.template_context source cursor actions

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 216)))) :=
  InitializerAllocations.template_heap source cursor actions heap valid

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := InitializerAllocations.template_scalars source cursor actions scalars

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (different : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocations.template_other source cursor actions key notHeap
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact different _ (by simp [symbols,topicAction,systemAction,nullAction,emptyAction,keyAction,headerAction,InitializerAllocations.constant])

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.template_other
