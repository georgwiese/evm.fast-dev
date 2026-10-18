import InitECandidate.Solver.MutableTable.SetModelPost
import InitECandidate.Solver.MutableTable.SetGrowTail
import InitECandidate.Solver.MutableTable.SetNoGrowthTail
import InitECandidate.Solver.MutableTable.MemoryModelEntry

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All original setter suffix paths: occupied update, absent insertion
without growth, or actual growth and insertion. The physical model and
original count/capacity arithmetic decide the paths. -/
theorem model_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat)
    (newValid : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 old.capacity))) →
      old.capacity < 2 * slots.length + 2 → Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (room : slots.length < old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (query value index : BitVec 64) (bits : Nat) (small : bits < 64) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (data : Insert.GeneralData source (cell old .header 0) (parameters kind old query) kind (cell old .values 0) (cell old .order 0) (cell old .position 0) (BitVec.ofNat 64 slots.length) bits slots)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query))) (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (selected : Find.Selection source (parameters kind old query) index) (bounded : index.toNat ≤ (parameters kind old query).capacity.toNat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (enough : afterGrowPrice kind old.capacity slots.length ≤ source.clock) :
    ∃ paid globals memory target plan next, paid ≤ afterGrowPrice kind old.capacity slots.length ∧
      (plan = old → paid ≤ Insert.rawPrice kind slots.length) ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (.val (.word 0#64))), target) ∧
      ModelPost source kind old start slots.length paid globals memory target plan next ∧ Valid kind plan := by
  let p := parameters kind old query
  have rawEnough : Insert.rawPrice kind slots.length ≤ source.clock := by
    dsimp only [afterGrowPrice, Insert.rawPrice] at enough ⊢
    omega
  have countNat : (BitVec.ofNat 64 slots.length).toNat = slots.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind old oldValid))]
  by_cases free : 2 * slots.length + 2 ≤ old.capacity
  · obtain ⟨paid, memory, target, paidBound, actual, frame, _, effect⟩ := no_growth_tail source (cell old .header 0) p kind
      (cell old .values 0) (cell old .order 0) (cell old .position 0) (BitVec.ofNat 64 slots.length) value index bits slots data tableLocal keyLocal valueLocal iLocal selected bounded
      (by rw [countNat]) (by rwa [← power]) insertCode rawEnough
    obtain ⟨next, shape, nextHeader, nextModel⟩ := MemoryModel.setter_effect source kind old oldValid domain little slots room header occupied query value memory effect
    have lengths : slots.length ≤ next.length ∧ next.length ≤ slots.length + 1 := by
      rcases shape with rfl | ⟨slot, rfl⟩ <;> simp
    refine ⟨paid, source.globals, memory, target, old, next, ?_, (by intro same; exact paidBound), actual,
      ModelPost.of_frame source kind old start slots.length paid source.globals memory target old next frame (Or.inl ⟨rfl, rfl⟩) lengths (by intro different; exact (different rfl).elim) (by intro initial; have high := lengths.2; omega) nextHeader nextModel
        (TableFootprint.setter_effect source kind old oldValid query _ value (by rw [countNat]; exact room) memory effect), oldValid⟩
    dsimp only [afterGrowPrice, Insert.rawPrice] at paidBound ⊢
    omega
  · have capRead := Find.table_read source (cell old .header 0) 16#64 p.capacity tableLocal (data.header.mapped 16 (by simp)) data.header.capacity
    by_cases absent : index = p.capacity
    · have skipped : evaluateHOLFiniteState source (.ite presentTest updateBranch .skip) = (none, source) := by
        simp only [eval] at capRead
        simp [evaluateHOLFiniteState_ite, presentTest, evalHOLExact, toExact, localVar, iLocal, capRead, absent,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have growthLayout := newValid (by rw [absent] at iLocal; exact iLocal) (by omega)
      obtain ⟨paid, memory, target, next, paidBound, actual, frame, length, nextHeader, nextModel, growFootprint⟩ := after_grow source kind old oldValid start growthLayout earlier domain little slots header occupied
        tableLocal query value keyLocal valueLocal data.queryFits data.queryMapped (by omega) heap bits power minimum allocCode zeroCode data.hashCode data.copyCode insertCode growCode enough
      refine ⟨paid, (GrowRuntime.callState source kind old start memory paid).globals, memory, target, relocated kind (old.base .header) start (2 * old.capacity), next,
        paidBound, ?_, ?_, ⟨frame, Or.inr ⟨rfl, rfl⟩, by omega, (by intro different; omega), (by intro initial; change 2 * next.length ≤ 2 * old.capacity; omega), nextHeader, nextModel, growFootprint⟩, growthLayout⟩
      · intro same
        have numeric := congrArg Plan.capacity same
        change 2 * old.capacity = old.capacity at numeric
        have positive := oldValid.positive
        omega
      · rw [afterIndex, StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
        exact actual
    · have unequal : index.toNat ≠ p.capacity.toNat := fun equal => absent (BitVec.eq_of_toNat_eq equal)
      have indexBound : index.toNat ≤ p.capacity.toNat := bounded
      have inside : index.toNat < p.capacity.toNat := by omega
      have capNat : p.capacity.toNat = old.capacity := by
        change (BitVec.ofNat 64 old.capacity).toNat = old.capacity
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small kind old oldValid)]
      have indexInside : index.toNat < old.capacity := by rwa [capNat] at inside
      have actual := update_execute source (cell old .header 0) (cell old .values 0) index p.capacity value tableLocal iLocal valueLocal
        (data.header.mapped 16 (by simp)) data.header.capacity data.valsMapped data.valsCell (data.slots index inside).valueMapped absent
      let memory := MemoryModel.valueMemory source.memory old index value
      let target := emptyLocalsHOLFinite {source with memory := memory}
      have frame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with globals := source.globals, memory := memory, clock := source.clock - 0} := by
        simp only [target, Nat.sub_zero, emptyLocalsHOLFinite]
      refine ⟨0, source.globals, memory, target, old, slots, Nat.zero_le _, (by intro same; exact Nat.zero_le _), actual, ?_⟩
      exact ⟨ModelPost.of_frame source kind old start slots.length 0 source.globals memory target old slots frame (Or.inl ⟨rfl, rfl⟩) ⟨Nat.le_refl _, by omega⟩ (by intro different; exact (different rfl).elim) (by intro initial; exact initial)
        (MemoryModel.Header.after_update source.memory kind old oldValid index value _ indexInside header)
        (MemoryModel.Occupied.after_update source kind old oldValid slots (Nat.le_of_lt room) occupied index value indexInside)
        (TableFootprint.updated source.memory kind old index value indexInside), oldValid⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_tail
