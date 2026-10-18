import InitECandidate.Solver.MutableTable.KeysAllocation

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def price (kind : KeyHash.Kind) (count : Nat) : Nat := (rowPrice kind + 1) * count + 1

/-- Entire original htab_keys, including both initial header reads, actual
allocation, padded copies, tuple return and all scopes. The original table
and every word outside the exact output allocation remain unchanged. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (start : Nat) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (outValid : MemoryRegion.Valid (outputRegion kind start slots.length)) (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ start)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : price kind slots.length ≤ source.clock) :
    ∃ paid memory target, paid ≤ price kind slots.length ∧
      evaluateHOLFiniteState source body = (some (.returned (pair (BitVec.ofNat 64 start) (BitVec.ofNat 64 slots.length))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (changed source kind start slots.length paid memory) ∧
      MemoryModel.PoolFrame source.memory memory kind plan ∧ MemoryModel.Occupied target kind plan slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ start + allocationSize kind slots.length ≤ query.toNat → memory query = source.memory query) := by
  let strided := bind source "stride" (BitVec.ofNat 64 (stride kind))
  let numbered := bind strided "n" (BitVec.ofNat 64 slots.length)
  let allocated := bind (changed numbered kind start slots.length 1 numbered.memory) "out" (BitVec.ofNat 64 start)
  have strideRead := MemoryModel.Header.read source kind plan valid domain _ header tableLocal 8 (by decide) (by decide) (BitVec.ofNat 64 (stride kind)) (by simp [MemoryModel.headerEntries])
  have stridedT : strided.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "stride" "t" _ (by decide)).trans tableLocal
  have countRead := MemoryModel.Header.read strided kind plan valid domain _ header stridedT 24 (by decide) (by decide) (BitVec.ofNat 64 slots.length) (by simp [MemoryModel.headerEntries])
  have numberedStride : numbered.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))) := (bind_lookup_other _ "n" "stride" _ (by decide)).trans (bind_lookup_same _ _ _)
  have numberedN : numbered.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 slots.length))) := bind_lookup_same _ _ _
  have sizeRead : eval numbered outputSize = some (.val (.word (BitVec.ofNat 64 (allocationSize kind slots.length)))) := by
    simp [eval, outputSize, localVar, evalHOLExact, evalListHOLExact, toExact, numberedStride, numberedN, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      allocationSize, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm]
  have args : evalListHOLFinite numbered (h := fun address => Classical.propDecidable (numbered.memaddrs address)) [outputSize] = some (PersistentAlloc.values (BitVec.ofNat 64 (allocationSize kind slots.length))) := by
    simp only [eval] at sizeRead
    simp [evalListHOLFinite, evalListHOLExact, sizeRead, PersistentAlloc.values]
  have allocationUpper : start + allocationSize kind slots.length ≤ 33806089496 := outValid.upper
  have pointerNat : (BitVec.ofNat 64 start).toNat = start := MemoryRegion.pointer_number _ outValid
  have amountNat : (BitVec.ofNat 64 (allocationSize kind slots.length)).toNat = allocationSize kind slots.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have callRun := PersistentAlloc.call_execute numbered "out" [outputSize] afterOutput (BitVec.ofNat 64 start) (BitVec.ofNat 64 (allocationSize kind slots.length)) args allocCode heap
    (by rw [pointerNat, amountNat]; exact allocationUpper) (by change 1 ≤ source.clock; dsimp only [price] at enough; omega)
  rw [allocated_state numbered kind start slots.length outValid] at callRun
  have allocatedT : allocated.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) :=
    (bind_lookup_other _ "out" "t" _ (by decide)).trans ((bind_lookup_other _ "n" "t" _ (by decide)).trans stridedT)
  have allocatedStride : allocated.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))) := (bind_lookup_other _ "out" "stride" _ (by decide)).trans numberedStride
  have allocatedN : allocated.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 slots.length))) := (bind_lookup_other _ "out" "n" _ (by decide)).trans numberedN
  have allocatedModel := MemoryModel.Occupied.of_fields source allocated kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, target, bounded, actual, frame, poolFrame, finalModel, outsideFrame⟩ := after_output_execute allocated kind plan valid domain start slots allocatedModel header outValid earlier allocatedT allocatedStride allocatedN (bind_lookup_same _ _ _) copyCode
    (by change (rowPrice kind + 1) * slots.length ≤ source.clock - 1; dsimp only [price] at enough; omega)
  change evaluateHOLFiniteState numbered (.decCall (ofString "out") .one (ofString "alloc") [outputSize] afterOutput) =
    (let output := evaluateHOLFiniteState allocated afterOutput; (output.1, restore numbered "out" output.2)) at callRun
  rw [actual] at callRun
  have nRun := Input.ScalarScope.declare_execute strided _ "n" (Find.tableLoad 24#64) (BitVec.ofNat 64 slots.length) (.decCall (ofString "out") .one (ofString "alloc") [outputSize] afterOutput) _ countRead callRun
  have strideRun := Input.ScalarScope.declare_execute source _ "stride" (Find.tableLoad 8#64) (BitVec.ofNat 64 (stride kind))
    (.dec (ofString "n") .one (Find.tableLoad 24#64) (.decCall (ofString "out") .one (ofString "alloc") [outputSize] afterOutput)) _ strideRead nRun
  let output := restore source "stride" (restore strided "n" (restore numbered "out" target))
  refine ⟨1 + paid, memory, output, ?_, ?_, ?_, poolFrame, MemoryModel.Occupied.of_fields target output kind plan slots finalModel rfl rfl rfl, outsideFrame⟩
  · dsimp only [price]; omega
  · rw [body_shape]; exact strideRun
  · change emptyLocalsHOLFinite target = _
    rw [frame]
    have subtract : source.clock - 1 - paid = source.clock - (1 + paid) := by omega
    simpa only [allocated, numbered, strided, changed, WitnessRadix.QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite, subtract]

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.execute
