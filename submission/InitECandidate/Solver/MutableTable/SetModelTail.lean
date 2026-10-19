import InitECandidate.Solver.MutableTable.SetModelTailValues
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
  obtain ⟨paid, globals, memory, target, plan, next, bounded, oldBound, run, post, valid, _⟩ :=
    model_tail_values source kind old oldValid start earlier domain little slots newValid room header occupied query value index
      (fun _=>True) (fun _ _ _ _ _=>True.intro) True.intro bits small power minimum data tableLocal keyLocal valueLocal iLocal
      selected bounded heap allocCode zeroCode insertCode growCode enough
  exact ⟨paid, globals, memory, target, plan, next, bounded, oldBound, run, post, valid⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_tail
