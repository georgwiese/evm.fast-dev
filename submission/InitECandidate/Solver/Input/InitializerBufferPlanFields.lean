import InitECandidate.Solver.Input.InitializerBufferFields

namespace InitECandidate.Solver.Input.InitializerAllocationAliases
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) :
    InitializerAllocations.context (template source cursor blocks) = InitializerAllocations.context source := by
  induction blocks generalizing source cursor with
  | nil => rfl
  | cons block rest ih => exact (ih (step source cursor block) (cursor + block.allocation.bytes)).trans (step_context source cursor block)

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor blocks).globals := by
  induction blocks generalizing source cursor with
  | nil => exact scalars
  | cons block rest ih => exact ih (step source cursor block) (cursor + block.allocation.bytes) (step_scalars source cursor block scalars)

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block)
    (valid : ∀ block ∈ blocks,Valid block)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor blocks).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + totalBytes blocks)))) := by
  induction blocks generalizing source cursor with
  | nil => simpa only [template,totalBytes,Nat.add_zero] using heap
  | cons block rest ih =>
    have tail := ih (step source cursor block) (cursor + block.allocation.bytes)
      (fun current member => valid current (List.mem_cons_of_mem _ member)) (step_heap source cursor block (valid block (by simp)) heap)
    simpa only [template,totalBytes,Nat.add_assoc] using tail

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor blocks = {template source cursor blocks with locals := locals} := by
  induction blocks generalizing source cursor with
  | nil => rfl
  | cons block rest ih =>
    simp only [template,step_locals]
    exact ih (step source cursor block) (cursor + block.allocation.bytes)

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) :
    (template source cursor blocks).locals = source.locals := by
  have same : {source with locals := source.locals} = source := rfl
  have preserved := congrArg (fun state => state.locals) (template_locals source cursor blocks source.locals)
  rw [same] at preserved
  exact preserved

theorem template_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) :
    (template source cursor blocks).memory = source.memory := by
  induction blocks generalizing source cursor with
  | nil => rfl
  | cons block rest ih => exact (ih (step source cursor block) (cursor + block.allocation.bytes)).trans (step_memory source cursor block)

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) (key : MlS)
    (heap : key ≠ ofString "heap_ptr")
    (allocations : ∀ block ∈ blocks,key ≠ ofString block.allocation.name)
    (aliases : ∀ block ∈ blocks,∀ action ∈ block.aliases,key ≠ ofString action.name) :
    (template source cursor blocks).globals.lookup key = source.globals.lookup key := by
  induction blocks generalizing source cursor with
  | nil => rfl
  | cons block rest ih =>
    have tail := ih (step source cursor block) (cursor + block.allocation.bytes)
      (fun current member => allocations current (List.mem_cons_of_mem _ member))
      (fun current member => aliases current (List.mem_cons_of_mem _ member))
    exact tail.trans (step_other source cursor block key heap (allocations block (by simp)) (aliases block (by simp)))

end InitECandidate.Solver.Input.InitializerAllocationAliases

#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_context
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_scalars
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_heap
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_locals
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_locals_value
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_memory
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_other
