import InitECandidate.Solver.MutableTable.SetNormalCallValues
import InitECandidate.Solver.MutableTable.SetNormalBound

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Actual successful original setter caller with derived allocation room
on its reached growth path and no entry-clock allowance. The precise
post-layout, physical model, ownership frame and smaller unchanged-layout
price remain available for global mutation accounting. -/
theorem model_call_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (half : 2 * slots.length ≤ old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (query value : BitVec 64) (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
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
    (setCode : source.code.lookup (ofString "htab_set") = some (TableCall.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (cell old .header 0) query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ paid globals memory plan next, paid ≤ modelPrice kind old.capacity slots.length + 1 ∧
      (plan = old → paid ≤ noGrowthPrice kind slots.length + 1) ∧ paid ≤ source.clock ∧
      ModelPost source kind old start slots.length paid globals memory target plan next ∧
      Valid kind plan ∧ 2 * next.length ≤ plan.capacity ∧ target.locals = source.locals := by
  obtain ⟨paid, globals, memory, plan, next, bounded, oldBound, fits, post, valid, nextHalf, locals, _⟩ :=
    model_call_bound_values source target kind old oldValid start startBound startAligned earlier domain little slots half header occupied
      query value (fun _=>True) (fun _ _ _ _ _=>True.intro) True.intro bits power minimum queryFits queryMapped heap
      allocCode trapCode zeroCode hashCode copyCode memeqCode findCode insertCode growCode setCode arguments args normal
  exact ⟨paid, globals, memory, plan, next, bounded, oldBound, fits, post, valid, nextHalf, locals⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_call_bound
