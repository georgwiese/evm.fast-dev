import InitECandidate.Solver.MutableTable.SetModelExecution

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

def modelCallState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat) (globals : HolFiniteMapExact MlS (ValueHOL 64)) (memory : WordWrites.Memory) :=
  {source with globals := globals, memory := memory, clock := source.clock - paid}

/-- Actual original setter ABI, including all growth choices and the
post-call half-capacity invariant required for repeated operations. Physical
entry ownership, potential allocation room and code/query/clock reachability
remain explicit; no execution or mutation result is assumed. -/
theorem model_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (half : 2 * slots.length ≤ old.capacity)
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (query value : BitVec 64) (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
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
    (enough : modelPrice kind old.capacity slots.length + 1 ≤ source.clock) :
    ∃ paid globals memory plan next, paid ≤ modelPrice kind old.capacity slots.length + 1 ∧
      (plan = old → paid ≤ noGrowthPrice kind slots.length + 1) ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, modelCallState source paid globals memory) ∧
      ModelPost source kind old start slots.length paid globals memory (modelCallState source paid globals memory) plan next ∧
      Valid kind plan ∧ 2 * next.length ≤ plan.capacity := by
  obtain ⟨newSmall, _, _⟩ := MemoryModel.growth_shape kind old oldValid bits power minimum
  have small : bits < 64 := by omega
  have room : slots.length < old.capacity := by have positive := oldValid.positive; omega
  obtain ⟨callee, called, tableLocal, keyLocal, valueLocal⟩ := TableCall.environment source.code.lookup (ofString "htab_set") body (cell old .header 0) query value setCode
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind old slots occupied rfl rfl rfl
  obtain ⟨paid, globals, memory, target, plan, next, bounded, oldBound, actual, post⟩ := model_execute entry kind old oldValid start newValid earlier domain little slots room header entryModel query value bits small power minimum queryFits queryMapped tableLocal keyLocal valueLocal heap
    allocCode zeroCode hashCode copyCode memeqCode findCode insertCode growCode (by change modelPrice kind old.capacity slots.length ≤ source.clock - 1; omega)
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "htab_set") arguments (TableCall.values (cell old .header 0) query value) body callee .one (.val (.word 0#64)) target
    args called (by omega) actual (by simp [shapeEqHOL, shapeOfHOLExact])
  have replaced : {target with locals := source.locals} = modelCallState source (paid + 1) globals memory := by
    have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) post.frame
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, modelCallState, subtract] using restored
  have memoryEq := congrArg PanSemStateFiniteExact.memory replaced
  have domainEq := congrArg PanSemStateFiniteExact.memaddrs replaced
  have endianEq := congrArg PanSemStateFiniteExact.be replaced
  have nextValid : Valid kind plan := by
    rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact oldValid
    · exact newValid
  refine ⟨paid + 1, globals, memory, plan, next, by omega, (by intro same; have boundedOld := oldBound same; omega), callRun.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => (none, state)) replaced), ?_, nextValid, post.half half⟩
  exact ⟨rfl, post.shape, post.countBound, post.grew, post.half, post.header,
    MemoryModel.Occupied.of_fields target _ kind plan next post.occupied memoryEq domainEq endianEq, post.footprint⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.model_call
