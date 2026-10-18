import InitECandidate.Solver.MutableTable.SetModelTail
import InitECandidate.Solver.MutableTable.SetNoGrowthExecution

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def modelPrice (kind : KeyHash.Kind) (capacity count : Nat) := Insert.findPrice kind count + afterGrowPrice kind capacity count

/-- Whole original setter body across every update/insert/grow decision.
Actual lookup and helper calls derive the returned physical model, heap
choice, item-count range and preservation of half-capacity occupancy. -/
theorem model_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
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
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (enough : modelPrice kind old.capacity slots.length ≤ source.clock) :
    ∃ paid globals memory target plan next, paid ≤ modelPrice kind old.capacity slots.length ∧
      (plan = old → paid ≤ noGrowthPrice kind slots.length) ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))), target) ∧
      ModelPost source kind old start slots.length paid globals memory target plan next := by
  let p := parameters kind old query
  have data := MemoryModel.runtime_data source kind old oldValid domain query slots room header occupied bits small power queryFits queryMapped little hashCode copyCode
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "t", localVar "key"] = some [.val (.word (cell old .header 0)), .val (.word query)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tableLocal, keyLocal]
  obtain ⟨findPaid, index, findBound, indexBound, callRun, selected⟩ := Insert.GeneralData.find_call source (cell old .header 0) p kind
    (cell old .values 0) (cell old .order 0) (cell old .position 0) (BitVec.ofNat 64 slots.length) bits slots data memeqCode findCode "i" [localVar "t", localVar "key"] afterIndex args
    (by dsimp only [modelPrice] at enough; omega)
  let resumed := WitnessRadix.QueryBranch.bind {source with clock := source.clock - findPaid} "i" index
  have resumedData := Insert.GeneralData.of_fields source resumed (cell old .header 0) p kind
    (cell old .values 0) (cell old .order 0) (cell old .position 0) (BitVec.ofNat 64 slots.length) bits slots data rfl rfl rfl rfl
  have resumedModel := MemoryModel.Occupied.of_fields source resumed kind old slots occupied rfl rfl rfl
  obtain ⟨tailPaid, globals, memory, post, plan, next, tailBound, tailOldBound, tailRun, tailPost, _⟩ := model_tail resumed kind old oldValid start earlier domain little slots (fun _ _ => newValid) room header resumedModel query value index bits small power minimum resumedData
    ((bind_lookup_other _ "i" "t" _ (by decide)).trans tableLocal) ((bind_lookup_other _ "i" "key" _ (by decide)).trans keyLocal)
    ((bind_lookup_other _ "i" "value" _ (by decide)).trans valueLocal) (bind_lookup_same _ _ _)
    (Find.Selection.of_fields source resumed p index rfl rfl rfl selected) indexBound heap allocCode zeroCode insertCode growCode
    (by change afterGrowPrice kind old.capacity slots.length ≤ source.clock - findPaid; dsimp only [modelPrice] at enough; omega)
  change evaluateHOLFiniteState source (.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex) =
    (let output := evaluateHOLFiniteState resumed afterIndex; (output.1, restore source "i" output.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨findPaid + tailPaid, globals, memory, restore source "i" post, plan, next, ?_, ?_, ?_, ?_⟩
  · dsimp only [modelPrice]
    omega
  · intro same
    have oldBound := tailOldBound same
    dsimp only [noGrowthPrice]
    omega
  · rw [body_shape]
    exact callRun
  · refine ⟨?_, tailPost.shape, tailPost.countBound, tailPost.grew, tailPost.half, tailPost.header,
      MemoryModel.Occupied.of_fields post (restore source "i" post) kind plan next tailPost.occupied rfl rfl rfl, tailPost.footprint⟩
    change emptyLocalsHOLFinite post = _
    rw [tailPost.frame]
    change emptyLocalsHOLFinite {source with globals := globals, memory := memory, clock := source.clock - findPaid - tailPaid} = _
    have subtract : source.clock - findPaid - tailPaid = source.clock - (findPaid + tailPaid) := by omega
    rw [subtract]

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_execute
