import InitECandidate.Solver.Input.InitializerFields

namespace InitECandidate.Solver.Input.InitializerAllocationAliases
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure Block where
  allocation : InitializerAllocations.Action
  aliases : List InitializerAliases.Action

structure Valid (block : Block) : Prop where
  allocation : InitializerAllocations.Valid block.allocation
  aliases : ∀ action,action ∈ block.aliases → InitializerAliases.Valid block.allocation.name action
  noHeap : ∀ action,action ∈ block.aliases → ofString action.name ≠ ofString "heap_ptr"

def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) :=
  InitializerAliases.template (InitializerAllocations.template source cursor [block.allocation]) (BitVec.ofNat 64 cursor) block.aliases
def withTail : List Block → ProgHOL 64 → ProgHOL 64
  | [],tail => tail
  | block :: rest,tail => InitializerAllocations.withTail [block.allocation] (InitializerAliases.withTail block.aliases (withTail rest tail))
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : List Block → PanSemStateFiniteExact 64 Guest.HostMemory
  | [] => source
  | block :: rest => template (step source cursor block) (cursor + block.allocation.bytes) rest
def totalBytes : List Block → Nat
  | [] => 0
  | block :: rest => block.allocation.bytes + totalBytes rest

theorem step_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (step source cursor block).globals :=
  InitializerAliases.template_scalars _ _ _ (InitializerAllocations.template_scalars source cursor [block.allocation] scalars)

theorem step_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) :
    InitializerAllocations.context (step source cursor block) = InitializerAllocations.context source := by
  unfold step
  rw [InitializerAliases.template_context,InitializerAllocations.template_context]

theorem step_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) (clock : Nat) :
    step {source with clock := clock} cursor block = {step source cursor block with clock := clock} := by
  unfold step
  rw [InitializerAllocations.template_clock,InitializerAliases.template_clock]

theorem step_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) (valid : Valid block)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (step source cursor block).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + block.allocation.bytes)))) := by
  have aliases := InitializerAliases.template_other (InitializerAllocations.template source cursor [block.allocation]) (BitVec.ofNat 64 cursor) block.aliases (ofString "heap_ptr")
    (fun action member => (valid.noHeap action member).symm)
  have allocated := InitializerAllocations.template_heap source cursor [block.allocation] heap
    (by intro action member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst action; exact valid.allocation)
  exact aliases.trans allocated

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) (clock : Nat) :
    template {source with clock := clock} cursor blocks = {template source cursor blocks with clock := clock} := by
  induction blocks generalizing source cursor with
  | nil => rfl
  | cons block rest ih =>
    simp only [template,step_clock]
    exact ih (step source cursor block) (cursor + block.allocation.bytes)

/-- One real assigned allocator call and all real aliases, with the current
scalar types and base binding derived from the allocator's actual result. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (block : Block) (tail : ProgHOL 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : Valid block) (room : cursor + block.allocation.bytes ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (InitializerAllocations.withTail [block.allocation] (InitializerAliases.withTail block.aliases tail)) =
      evaluateHOLFiniteState {step source cursor block with clock := source.clock - 1} tail := by
  have allocatedRun := InitializerAllocations.execute_prefix source cursor [block.allocation] (InitializerAliases.withTail block.aliases tail) installed scalars heap
    (by intro action member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; subst action; exact valid.allocation)
    (by simpa only [InitializerAllocations.totalBytes,Nat.add_zero] using room) aligned enough
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at allocatedRun
  let allocated := InitializerAllocations.template source cursor [block.allocation]
  let ready := {allocated with clock := source.clock - 1}
  have binding : ready.globals.lookup (ofString block.allocation.name) = some (.val (.word (BitVec.ofNat 64 cursor))) := by
    simp only [ready,allocated,InitializerAllocations.template_globals]
    simp [InitializerAllocations.globalTemplate,HolFiniteMapExact.update,FUPDATE]
  have aliasesRun := InitializerAliases.execute_prefix ready block.allocation.name (BitVec.ofNat 64 cursor) block.aliases tail
    (InitializerAllocations.template_scalars source cursor [block.allocation] scalars) binding valid.aliases
  simp only [ready,InitializerAliases.template_clock] at aliasesRun
  exact allocatedRun.trans aliasesRun

/-- Execute a literal plan of allocations and aliases against original code.
There is one source tick per actual allocator call; assignments remain in AST. -/
theorem execute_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (blocks : List Block) (tail : ProgHOL 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (valid : ∀ block,block ∈ blocks → Valid block) (room : cursor + totalBytes blocks ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : blocks.length ≤ source.clock) :
    evaluateHOLFiniteState source (withTail blocks tail) = evaluateHOLFiniteState {template source cursor blocks with clock := source.clock - blocks.length} tail := by
  induction blocks generalizing source cursor with
  | nil => rfl
  | cons block rest ih =>
    have current := valid block (by simp)
    have first := step_execute source cursor block (withTail rest tail) installed scalars heap current
      (by change cursor + (block.allocation.bytes + totalBytes rest) ≤ 33806089496 at room; omega) aligned (by simp only [List.length_cons] at enough; omega)
    let next := {step source cursor block with clock := source.clock - 1}
    have nextInstalled := InitializerAllocations.installed_of_context source next
      ((InitializerAllocations.context_clock (step source cursor block) (source.clock - 1)).trans (step_context source cursor block)) installed
    have nextAligned : (cursor + block.allocation.bytes) % 8 = 0 := by have := current.allocation.aligned; omega
    have following := ih next (cursor + block.allocation.bytes) nextInstalled (step_scalars source cursor block scalars) (step_heap source cursor block current heap)
      (fun item member => valid item (List.mem_cons_of_mem _ member)) (by change cursor + (block.allocation.bytes + totalBytes rest) ≤ 33806089496 at room; omega)
      nextAligned (by change rest.length ≤ source.clock - 1; simp only [List.length_cons] at enough; omega)
    have clocks : source.clock - 1 - rest.length = source.clock - (block :: rest).length := by simp only [Nat.sub_sub,List.length_cons,Nat.add_comm]
    simp only [next,template_clock,clocks] at following
    exact first.trans following

end InitECandidate.Solver.Input.InitializerAllocationAliases

#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_scalars
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_context
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_clock
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_heap
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.template_clock
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.step_execute
#print axioms InitECandidate.Solver.Input.InitializerAllocationAliases.execute_prefix
