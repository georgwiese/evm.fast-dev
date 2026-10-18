import InitECandidate.Solver.MutableTable.CopyModel

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Complete original body contract with exact copy price/reservation,
both physical table models and every outside-allocation word preserved. -/
theorem execute_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (nextValid : Valid kind (fresh kind start old.capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) (slots : List Nat) (occupied : MemoryModel.Occupied source kind old slots)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : price kind old.capacity ≤ source.clock) :
    ∃ memory target,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word (BitVec.ofNat 64 start)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (changed source kind old start (price kind old.capacity) memory) ∧
      MemoryModel.Header memory kind (fresh kind start old.capacity) (BitVec.ofNat 64 slots.length) ∧
      MemoryModel.Occupied (changed source kind old start (price kind old.capacity) memory) kind (fresh kind start old.capacity) slots ∧
      MemoryModel.PoolFrame source.memory memory kind old ∧
      MemoryModel.Occupied (changed source kind old start (price kind old.capacity) memory) kind old slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ freshEnd kind start old.capacity ≤ query.toNat → memory query = source.memory query) := by
  let next := fresh kind start old.capacity
  let entered := initial source kind old
  let completed := finalState source kind old start
  have exactPrice := exact_price kind old next oldValid nextValid shape
  obtain ⟨target, actual, rawFrame, clock, oldFrame⟩ := execute source kind old oldValid start nextValid earlier domain _ header tableLocal heap allocCode copyCode
    (by rw [exactPrice]; exact enough)
  have canonicalFrame := final_frame source kind old start
  rw [exactPrice] at canonicalFrame
  have memoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) rawFrame
  change target.memory = completed.memory at memoryEq
  have allEarlier : ∀ first second, old.base first + size kind old first ≤ next.base second := by
    intro first second
    have ordered := earlier first
    cases second <;> dsimp only [next, fresh] <;> omega
  have entryModel := MemoryModel.Occupied.of_fields source entered kind old slots occupied rfl rfl rfl
  have newModel := copied_occupied entered kind old next oldValid nextValid rfl allEarlier domain little shape slots entryModel
  have newHeader := copied_header entered kind old next oldValid nextValid rfl allEarlier (BitVec.ofNat 64 slots.length) header
  have domainEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) canonicalFrame
  have endianEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) canonicalFrame
  refine ⟨completed.memory, target, actual, rawFrame.trans canonicalFrame, newHeader, ?_, ?_, ?_, ?_⟩
  · exact MemoryModel.Occupied.of_fields completed _ kind next slots newModel rfl domainEq endianEq
  · rw [memoryEq] at oldFrame
    exact oldFrame
  · apply MemoryModel.Occupied.of_pool_frame source (changed source kind old start (price kind old.capacity) completed.memory) kind old oldValid slots occupied rfl rfl
    rw [memoryEq] at oldFrame
    exact oldFrame
  · intro query outside
    exact final_away source kind old start nextValid query outside

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.execute_model
