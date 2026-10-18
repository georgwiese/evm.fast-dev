import InitECandidate.Solver.MutableTable.DeleteModelTail
import InitECandidate.Solver.MutableTable.MemoryModelEntry
import InitECandidate.Solver.MutableTable.InsertSelection

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def modelPrice (kind : KeyHash.Kind) (count : Nat) : Nat := Insert.findPrice kind count + tailPrice kind count

/-- Entire unchanged htab_del body: actual lookup, absent/present choice,
all original headers and scans, final stores, scopes and physical result. -/
theorem model_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (enough : modelPrice kind slots.length ≤ source.clock) :
    ∃ paid memory target next flag, paid ≤ modelPrice kind slots.length ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word flag))), target) ∧
      ModelPost source kind plan slots paid memory target next flag := by
  let p := parameters kind plan query
  have data := MemoryModel.runtime_data source kind plan valid domain query slots room header occupied bits small power queryFits queryMapped little hashCode copyCode
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t", localVar "key"] =
      some [.val (.word (cell plan .header 0)), .val (.word query)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tableLocal, keyLocal]
  obtain ⟨findPaid, index, findBound, indexBound, callRun, selected⟩ := Insert.GeneralData.find_call source (cell plan .header 0) p kind
    (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) (BitVec.ofNat 64 slots.length) bits slots data memeqCode findCode "i" [localVar "t", localVar "key"] afterIndex args
    (by dsimp only [modelPrice] at enough; omega)
  let resumed := bind {source with clock := source.clock - findPaid} "i" index
  have resumedModel := MemoryModel.Occupied.of_fields source resumed kind plan slots occupied rfl rfl rfl
  obtain ⟨tailPaid, memory, target, next, flag, tailBound, tailRun, tailPost⟩ := model_tail resumed kind plan valid domain little slots room resumedModel bits small power header index
    ((bind_lookup_other _ "i" "t" _ (by decide)).trans tableLocal) (bind_lookup_same _ _ _)
    (fun present => (Insert.GeneralData.selected_slot source (cell plan .header 0) p kind _ _ _ _ bits slots data index selected present).2)
    hashCode copyCode (by change tailPrice kind slots.length ≤ source.clock - findPaid; dsimp only [modelPrice] at enough; omega)
  change evaluateHOLFiniteState source (.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex) =
    (let output := evaluateHOLFiniteState resumed afterIndex; (output.1, restore source "i" output.2)) at callRun
  rw [tailRun] at callRun
  refine ⟨findPaid + tailPaid, memory, restore source "i" target, next, flag, ?_, ?_, ?_⟩
  · dsimp only [modelPrice]; omega
  · rw [body_shape]; exact callRun
  · refine ⟨?_, tailPost.shape, tailPost.header, MemoryModel.Occupied.of_fields target _ kind plan next tailPost.occupied rfl rfl rfl⟩
    change emptyLocalsHOLFinite target = _
    rw [tailPost.frame]
    change emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - findPaid - tailPaid} = _
    rw [Nat.sub_sub]

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_execute
