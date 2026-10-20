import InitECandidate.Solver.Input.MainBlsFpInitialization
import InitECandidate.Solver.Input.MainBlsPairInitialization

namespace InitECandidate.Solver.Input.Main.BlsFpInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem template_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) :
    (template source cursor constants).globals = (allocated source cursor).globals := by simp only [template,memoryTemplate]

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) :
    InitializerAllocations.context (template source cursor constants) = InitializerAllocations.context source := by
  unfold template memoryTemplate
  rw [InitializerAllocations.context_memory]
  exact InitializerAllocationAliases.step_context source cursor block

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor constants).globals := by
  rw [template_globals]
  exact InitializerAllocationAliases.step_scalars source cursor block scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor constants).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 240)))) := by
  rw [template_globals]
  exact InitializerAllocationAliases.step_heap source cursor block valid heap

theorem template_constants (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) :
    (template source cursor constants).globals.lookup (ofString "bls_c") = source.globals.lookup (ofString "bls_c") := by
  rw [template_globals]
  exact allocated_constants source cursor

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor constants).globals.lookup key = source.globals.lookup key := by
  rw [template_globals]
  apply InitializerAllocationAliases.step_other source cursor block key heap (other _ (by simp [symbols,block,InitializerAllocations.constant]))
  intro action member
  simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact other _ (by simp [symbols,InitializerAliases.direct,InitializerAliases.offset])

end InitECandidate.Solver.Input.Main.BlsFpInitialization

namespace InitECandidate.Solver.Input.Main.BlsPairInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) :
    InitializerAllocations.context (template source cursor kind) = InitializerAllocations.context source := InitializerAllocationAliases.step_context source cursor (block kind)

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor kind).globals := InitializerAllocationAliases.step_scalars source cursor (block kind) scalars

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor kind).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 192)))) := InitializerAllocationAliases.step_heap source cursor (block kind) (valid kind) heap

theorem template_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) :
    (template source cursor kind).globals.lookup (ofString (paramsName kind)) = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  unfold template InitializerAllocationAliases.step
  have aliases := InitializerAliases.template_other (InitializerAllocations.template source cursor [(block kind).allocation]) (BitVec.ofNat 64 cursor) (block kind).aliases (ofString (paramsName kind))
    (by intro action member; exact ((valid kind).aliases action member).different.symm)
  exact aliases.trans (WordTableInitialization.allocated_binding source cursor (block kind).allocation)

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor kind).globals.lookup key = source.globals.lookup key := by
  apply InitializerAllocationAliases.step_other source cursor (block kind) key heap ?_ ?_
  · apply other
    cases kind <;> simp [block,paramsName,symbols,InitializerAllocations.constant]
  · intro action member
    simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals apply other
    all_goals cases kind <;> simp [symbols,firstName,secondName,InitializerAliases.direct,InitializerAliases.offset]

theorem template_constants (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (kind : Kind) :
    (template source cursor kind).globals.lookup (ofString "bls_c") = source.globals.lookup (ofString "bls_c") := by
  apply template_other source cursor kind (ofString "bls_c") (by decide)
  intro name member
  simp only [symbols,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end InitECandidate.Solver.Input.Main.BlsPairInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_globals
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_constants
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_binding
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.template_constants
