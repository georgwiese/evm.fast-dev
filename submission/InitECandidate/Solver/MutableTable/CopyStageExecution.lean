import InitECandidate.Solver.MutableTable.CopyStageReads

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

theorem CoreLocals.allocated {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (old next : Plan) (pool : Pool)
    (locals : CoreLocals source kind old) : CoreLocals (allocated source kind next pool) kind old := by
  constructor
  · exact (bind_lookup_other _ (name pool) "t" _ (by cases pool <;> decide)).trans locals.table
  · exact (bind_lookup_other _ (name pool) "cap" _ (by cases pool <;> decide)).trans locals.cap
  · exact (bind_lookup_other _ (name pool) "stride" _ (by cases pool <;> decide)).trans locals.stride

/-- One original allocation/copy/pointer-rewrite stage executes from actual
header reads, derived allocator guards and mapped regions. -/
theorem stage_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : BitVec 64) (header : MemoryModel.Header source.memory kind old count)
    (locals : CoreLocals source kind old) (pool : Pool)
    (newHeader : pool ≠ .header → source.locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (next.base pool)))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : stagePrice kind old next pool ≤ source.clock) :
    ∃ restoreStack, Executes source (stageActions pool) (stageState source kind old next pool) restoreStack := by
  classical
  let alloc := allocated source kind next pool
  let copy := copied source kind old next pool
  have nextRoom : amount kind old.capacity pool ≤ size kind next pool := by rw [← sameCapacity]; exact amount_room kind next pool
  have oldRoom := amount_room kind old pool
  have nextFits := nextValid.upper pool
  have roundBounds := rounded_bounds (amount kind old.capacity pool)
  have rounded : rounded (amount kind old.capacity pool) = size kind next pool := by rw [← sameCapacity]; exact amount_round kind next pool
  rw [rounded] at roundBounds
  have endAligned : (next.base pool + size kind next pool) % 8 = 0 := by
    simp only [Nat.add_mod, nextValid.aligned pool, roundBounds.2.2, Nat.zero_add]
  have funded : CopyGeneral.cost (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool) + 1 ≤ alloc.clock := by
    change _ ≤ source.clock - 1
    unfold stagePrice at enough
    omega
  have allocLocals := CoreLocals.allocated source kind old next pool locals
  have srcRead := source_read alloc kind old oldValid domain count header allocLocals.table pool
  have sizeRead := amount_read alloc kind old allocLocals pool
  have dstRead : eval alloc (localVar (name pool)) = some (.val (.word (cell next pool 0))) := by
    have bound : alloc.locals.lookup (ofString (name pool)) = some (.val (.word (cell next pool 0))) := by
      simpa only [cell, Nat.add_zero, alloc, copy, copied, CopyGeneral.callState, allocated, PersistentAlloc.nextState] using bind_lookup_same
        {source with globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool)))), clock := source.clock - 1}
        (name pool) (BitVec.ofNat 64 (next.base pool))
    simp [eval, localVar, evalHOLExact, toExact, bound]
  have args : evalListHOLFinite alloc (h := fun address => Classical.propDecidable (alloc.memaddrs address))
      [localVar (name pool), sourceExpression pool, amountExpression pool] = some (CopyGeneral.values (cell next pool 0) (cell old pool 0) (amount kind old.capacity pool)) := by
    simp only [eval] at srcRead sizeRead dstRead
    simp [evalListHOLFinite, evalListHOLExact, srcRead, sizeRead, dstRead, CopyGeneral.values]
  have mapped : CopyContext.Mapped alloc (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool) := by
    rw [← region_pointer kind old pool, ← region_pointer kind next pool]
    exact MemoryRegion.copy_mapped alloc domain _ _ (MemoryRegion.pool_valid kind old oldValid pool) (MemoryRegion.pool_valid kind next nextValid pool) _ oldRoom nextRoom
  have oldUpper := oldValid.upper pool
  have small : amount kind old.capacity pool + 32 < 2 ^ 64 := by omega
  have copyRun := CopyGeneral.call_execute alloc _ (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool) args copyCode mapped small funded
  change evaluateHOLFiniteState alloc (copyCall pool) = (none, copy) at copyRun
  have copyClock : copy.clock ≤ alloc.clock := Nat.sub_le _ _
  have afterCopy : Executes copy (if pool = .header then [] else [.command (pointerStore pool)]) (stageState source kind old next pool) id := by
    by_cases isHeader : pool = .header
    · simp only [if_pos isHeader, stageState]
      exact .done _
    · rw [if_neg isHeader]
      have nLocal : copy.locals.lookup (ofString "n") = some (.val (.word (cell next .header 0))) := by
        exact (bind_lookup_other _ (name pool) "n" _ (by cases pool <;> first | exact False.elim (isHeader rfl) | decide)).trans (newHeader isHeader)
      have nameLocal : copy.locals.lookup (ofString (name pool)) = some (.val (.word (cell next pool 0))) := by
        simpa only [cell, Nat.add_zero, alloc, copy, copied, CopyGeneral.callState, allocated, PersistentAlloc.nextState] using bind_lookup_same
          {source with globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (next.base pool + size kind next pool)))), clock := source.clock - 1}
          (name pool) (BitVec.ofNat 64 (next.base pool))
      have addressRead : eval copy (.op .add [localVar "n", .const (BitVec.ofNat 64 (headerOffset pool))]) = some (.val (.word (cell next .header (headerOffset pool)))) := by
        simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, nLocal, valueIsWord, valueWord, wordOpHOL, wordOp, constant_cell]
      have valueRead : eval copy (localVar (name pool)) = some (.val (.word (cell next pool 0))) := by
        simp [eval, localVar, evalHOLExact, toExact, nameLocal]
      have fieldInside : headerOffset pool < size kind next .header := by cases pool <;> norm_num [headerOffset, size]
      have fieldAligned : headerOffset pool % 8 = 0 := by cases pool <;> decide
      have fieldMapped : copy.memaddrs (cell next .header (headerOffset pool)) := by
        rw [show copy.memaddrs = source.memaddrs from rfl, domain]
        exact NaturalLayout.mapped kind next nextValid .header _ fieldInside fieldAligned
      have stored := StoreWord.execute copy _ _ _ _ addressRead valueRead fieldMapped
      change evaluateHOLFiniteState copy (pointerStore pool) = _ at stored
      have post : stageState source kind old next pool = {copy with memory := StoreWord.put copy.memory (cell next .header (headerOffset pool)) (cell next pool 0)} := if_neg isHeader
      rw [post]
      exact .command stored (Nat.le_refl _) (.done _)
  refine ⟨fun target => restore source (name pool) target, ?_⟩
  unfold stageActions
  simp only [List.cons_append, List.nil_append]
  apply PersistentAlloc.prefix_allocate source _ (name pool) (amountExpression pool) _ id (next.base pool) (amount kind old.capacity pool) (next.base pool + size kind next pool)
    (amount_read source kind old locals pool) allocCode heap (by omega) (by omega) (by omega) endAligned (by unfold stagePrice at enough; omega)
  exact .command copyRun copyClock afterCopy

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.CoreLocals.allocated
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_executes
