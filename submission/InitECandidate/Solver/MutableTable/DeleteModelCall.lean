import InitECandidate.Solver.MutableTable.DeleteEnvironment

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

def modelCallState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat) (memory : WordWrites.Memory) :=
  {source with memory := memory, clock := source.clock - paid}

/-- Real ignored-result deletion caller, as used by the unchanged guest.
The original physical table survives with zero or one fewer entries and no
change to its layout, heap cursor, globals or other nonlocal fields. -/
theorem model_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (enough : modelPrice kind slots.length + 1 ≤ source.clock) :
    ∃ paid memory next flag, paid ≤ modelPrice kind slots.length + 1 ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, modelCallState source paid memory) ∧
      ModelPost source kind plan slots paid memory (modelCallState source paid memory) next flag ∧
      (2 * slots.length ≤ plan.capacity → 2 * next.length ≤ plan.capacity) := by
  obtain ⟨callee, called, tableLocal, keyLocal⟩ := environment source.code.lookup (cell plan .header 0) query deleteCode
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, target, next, flag, bounded, actual, post⟩ := model_execute entry kind plan valid domain little slots room entryModel bits small power header query queryFits queryMapped tableLocal keyLocal
    hashCode copyCode memeqCode findCode (by change modelPrice kind slots.length ≤ source.clock - 1; omega)
  have callRun := ignored_memory_call source target (ofString "htab_del") .one arguments _ body callee (.val (.word flag)) paid memory
    args called (by omega) actual (by simp [shapeOfHOLExact, shapeEqHOL]) post.frame
  have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  have replaced : {target with locals := source.locals} = modelCallState source (paid + 1) memory := by
    have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) post.frame
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, modelCallState, subtract] using restored
  have memoryEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) replaced
  have domainEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) replaced
  have endianEq := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) replaced
  refine ⟨paid + 1, memory, next, flag, by omega, ?_, ?_, ?_⟩
  · simpa only [modelCallState, subtract] using callRun
  · exact ⟨rfl, post.shape, post.header, MemoryModel.Occupied.of_fields target _ kind plan next post.occupied memoryEq domainEq endianEq⟩
  · intro half
    have high := (ModelPost.count_bound entry kind plan slots paid memory target next flag post).2
    omega

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_call
