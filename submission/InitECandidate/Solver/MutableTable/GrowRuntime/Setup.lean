import InitECandidate.Solver.MutableTable.GrowRuntime.Prepared

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

theorem setup_shape (plan : Plan) : Grow.body = program (Grow.actions.take 7)
    (program allocationActions (.seq clearCall (FieldStores.program "t" "" (resetFields plan) Grow.afterSetup))) := by
  rw [Grow.body_shape]
  rfl

set_option maxHeartbeats 1000000 in
/-- Entire real growth setup up to the rehash loop: header reads, five
allocations, memzero, seven stores and the scoped zero loop counter. Lexical
restorations are retained for every possible continuation outcome. -/
theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start count : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (multiple : (2 * old.capacity) % 8 = 0)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : setupPrice (2 * old.capacity) ≤ source.clock) :
    ∃ restoreStack : PanSemStateFiniteExact 64 Guest.HostMemory → PanSemStateFiniteExact 64 Guest.HostMemory,
      (∀ target, emptyLocalsHOLFinite (restoreStack target) = emptyLocalsHOLFinite target) ∧
      evaluateHOLFiniteState source Grow.body =
        (let output := evaluateHOLFiniteState (preparedState source kind old start count) (.seq Grow.loop Grow.returnZero)
         (output.1, restoreStack output.2)) := by
  let plan := relocated kind (old.base .header) start (2 * old.capacity)
  let headers := headerState source kind old count
  let allocated := allocatedState headers kind start (2 * old.capacity)
  let cleared := clearState allocated plan
  let reset := {allocated with memory := (resetMemory source.memory plan), clock := allocated.clock - (Zero.price plan.capacity + 1)}
  obtain ⟨restoreHeader, headerSetup⟩ := header_execute source kind old oldValid domain count header tableLocal
  obtain ⟨restoreArrays, arraySetup⟩ := allocations_execute headers kind (old.base .header) start (2 * old.capacity) newValid
    (header_amount source kind old count) heap allocCode (by change 5 ≤ source.clock; dsimp only [setupPrice] at enough; omega)
  have arrays : ArrayLocals allocated plan := allocated_arrays headers kind (old.base .header) start (2 * old.capacity)
  have cap : allocated.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 (2 * old.capacity)))) :=
    (allocated_other headers kind start (2 * old.capacity) "ncap" (by intro saved member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)).trans (header_amount source kind old count).cap
  have table : allocated.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := by
    have actual := (prepared_locals source kind old start count tableLocal).table
    change (WitnessRadix.QueryBranch.bind reset "k" 0#64).locals.lookup (ofString "t") = _ at actual
    rw [bind_lookup_other reset "k" "t" 0#64 (by decide)] at actual
    exact actual
  have clearRun := clear_execute allocated kind plan newValid domain multiple arrays.used cap zeroCode
    (by change Zero.price (2 * old.capacity) + 1 ≤ source.clock - 1 - 1 - 1 - 1 - 1; dsimp only [setupPrice] at enough; omega)
  have storeRun := stores_execute cleared kind plan newValid domain table cap arrays.keys arrays.vals arrays.used arrays.order arrays.position Grow.afterSetup
  have allocatedMemory : allocated.memory = source.memory := rfl
  have storedEq : {cleared with memory := WordWrites.write cleared.memory (resetWrites plan)} = reset := by
    dsimp only [cleared, clearState, reset, resetMemory]
    simp only [allocatedMemory]
  rw [storedEq] at storeRun
  have preparedEq : WitnessRadix.QueryBranch.bind reset "k" 0#64 = preparedState source kind old start count := rfl
  have counterSetup : Executes reset [.declare "k" (.const 0#64)] (WitnessRadix.QueryBranch.bind reset "k" 0#64)
      (fun target => restore reset "k" target) := .declare 0#64 rfl (.done _)
  have counterRun := WitnessRadix.ProgramPrefix.execute counterSetup (.seq Grow.loop Grow.returnZero)
  rw [preparedEq] at counterRun
  change evaluateHOLFiniteState reset Grow.afterSetup = _ at counterRun
  have tailRun : evaluateHOLFiniteState allocated (.seq clearCall (FieldStores.program "t" "" (resetFields plan) Grow.afterSetup)) =
      (let output := evaluateHOLFiniteState (preparedState source kind old start count) (.seq Grow.loop Grow.returnZero)
       (output.1, restore reset "k" output.2)) := by
    rw [StateSteps.next_sequence allocated cleared clearCall _ clearRun (by change allocated.clock - (Zero.price plan.capacity + 1) ≤ allocated.clock; omega)]
    rw [storeRun, counterRun]
  refine ⟨(fun target => restoreHeader (restoreArrays (restore reset "k" target))), ?_, ?_⟩
  · intro target
    rw [WitnessRadix.ProgramPrefix.restoration_frame headerSetup, WitnessRadix.ProgramPrefix.restoration_frame arraySetup]
    rfl
  · rw [setup_shape plan, WitnessRadix.ProgramPrefix.execute headerSetup, WitnessRadix.ProgramPrefix.execute arraySetup, tailRun]

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.setup_shape
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.setup_execute
