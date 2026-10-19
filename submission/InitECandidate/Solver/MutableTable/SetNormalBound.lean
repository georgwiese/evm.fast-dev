import InitECandidate.Solver.MutableTable.SetNormalBoundValues
import InitECandidate.Solver.MutableTable.SetNormalExecution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Bound an actual normal original setter without an entry clock allowance
or a prospective new-layout premise. Exact add-clock equality funds the
constructive proof and strips the padding afterward. -/
theorem model_body_bound (source actualTarget : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (query value : BitVec 64) (bits : Nat) (small : bits < 64) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query))) (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (actualValue : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned actualValue), actualTarget)) :
    ∃ paid globals memory plan next, paid ≤ modelPrice kind old.capacity slots.length ∧
      (plan = old → paid ≤ noGrowthPrice kind slots.length) ∧ paid ≤ source.clock ∧ actualValue = .val (.word 0#64) ∧
      ModelPost source kind old start slots.length paid globals memory actualTarget plan next ∧ Valid kind plan := by
  obtain ⟨paid, globals, memory, plan, next, bounded, oldBound, fits, resultEq, post, valid, _⟩ :=
    model_body_bound_values source actualTarget kind old oldValid start startBound startAligned earlier domain little slots room header occupied
      query value (fun _=>True) (fun _ _ _ _ _=>True.intro) True.intro bits small power minimum queryFits queryMapped tableLocal keyLocal valueLocal heap
      allocCode trapCode zeroCode hashCode copyCode memeqCode findCode insertCode growCode actualValue normal
  exact ⟨paid, globals, memory, plan, next, bounded, oldBound, fits, resultEq, post, valid⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_body_bound
