import InitECandidate.Solver.Input.InitializerAllocationAliases
import InitECandidate.Solver.Input.InitializerMemoryFrame

namespace InitECandidate.Solver.Input.InitializerAliases
open Flapjack PanSemStateFiniteExact

theorem template_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) :
    (template source pointer actions).memory = source.memory := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source pointer action)

end InitECandidate.Solver.Input.InitializerAliases

namespace InitECandidate.Solver.Input.InitializerAllocationAliases
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem step_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    step {source with locals := locals} cursor block = {step source cursor block with locals := locals} := by
  unfold step
  rw [InitializerAllocations.template_locals source cursor [block.allocation] locals]
  exact InitializerAliases.template_locals (InitializerAllocations.template source cursor [block.allocation]) (BitVec.ofNat 64 cursor) block.aliases locals

theorem step_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) :
    (step source cursor block).locals = source.locals := by
  unfold step
  rw [InitializerAliases.template_locals_value,InitializerAllocations.template_locals_value]

theorem step_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) :
    (step source cursor block).clock = source.clock := by
  unfold step
  rw [InitializerAliases.template_clock_value,InitializerAllocations.template_clock_value]

theorem step_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) :
    (step source cursor block).memory = source.memory := by
  unfold step
  rw [InitializerAliases.template_memory,InitializerAllocations.template_memory]

theorem step_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (allocation : key ≠ ofString block.allocation.name)
    (aliases : ∀ action ∈ block.aliases,key ≠ ofString action.name) :
    (step source cursor block).globals.lookup key = source.globals.lookup key := by
  unfold step
  rw [InitializerAliases.template_other _ _ _ key aliases]
  apply InitializerAllocations.template_other source cursor [block.allocation] key heap
  intro action member
  have same := List.mem_singleton.mp member
  subst action
  exact allocation

end InitECandidate.Solver.Input.InitializerAllocationAliases

#print axioms InitECandidate.Solver.Input.InitializerAliases.template_memory
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_locals
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_locals_value
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_clock_value
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_memory
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_other
