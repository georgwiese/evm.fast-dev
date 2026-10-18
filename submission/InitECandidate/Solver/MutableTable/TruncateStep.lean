import InitECandidate.Solver.MutableTable.TruncateReads

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete literal truncate iteration: real last ordinal and slot reads,
actual own-key argument, unchanged htab_del caller and both scope restores.
This does not assume that self-deletion succeeds. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (positive : 0 < slots.length) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (enough : Delete.modelPrice kind slots.length + 1 ≤ source.clock) :
    ∃ paid memory next flag, paid ≤ Delete.modelPrice kind slots.length + 1 ∧
      evaluateHOLFiniteState source loopBody = (none, Delete.modelCallState source paid memory) ∧
      Delete.ModelPost source kind plan slots paid memory (Delete.modelCallState source paid memory) next flag := by
  let ordinal : Fin slots.length := ⟨slots.length - 1, by omega⟩
  let slot := slots.get ordinal
  let ps := bind source "pos" (BitVec.ofNat 64 (slots.length - 1))
  let ss := bind ps "slot" (BitVec.ofNat 64 slot)
  let query := cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (stride kind)
  have slotInside : slot < plan.capacity := occupied.inside _ (List.get_mem slots ordinal)
  have ordinalInside : slots.length - 1 < plan.capacity := by omega
  have slotVector : (BitVec.ofNat 64 slot).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans slotInside (capacity_small kind plan valid))]
    exact slotInside
  have countRead := MemoryModel.Header.read source kind plan valid domain _ header tableLocal 24 (by decide) (by decide) (BitVec.ofNat 64 slots.length) (by simp [MemoryModel.headerEntries])
  have subtract : BitVec.ofNat 64 slots.length - 1#64 = BitVec.ofNat 64 (slots.length - 1) :=
    BitVec.ofNat_sub_ofNat_of_le slots.length 1 (by decide) positive
  have lastRead : eval source lastPosition = some (.val (.word (BitVec.ofNat 64 (slots.length - 1)))) := by
    simp only [eval] at countRead
    simp [eval, lastPosition, evalHOLExact, evalListHOLExact, toExact, countRead, valueIsWord, valueWord, wordOpHOL, wordOp, subtract]
  have psT : ps.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "pos" "t" _ (by decide)).trans tableLocal
  have orderHeader := MemoryModel.Header.read ps kind plan valid domain _ header psT 56 (by decide) (by decide) (cell plan .order 0) (by simp [MemoryModel.headerEntries])
  have orderMapped : ps.memaddrs (cell plan .order 0 + BitVec.ofNat 64 (slots.length - 1) * 8#64) := by
    rw [Delete.Move.natural_word_address kind plan valid .order _ ordinalInside]
    change source.memaddrs _
    rw [domain]
    exact mapped kind plan valid .order _ (by change 8 * (slots.length - 1) < 8 * plan.capacity; omega) (by omega)
  have orderStored : ps.memory (cell plan .order 0 + BitVec.ofNat 64 (slots.length - 1) * 8#64) = .word (BitVec.ofNat 64 slot) := by
    rw [Delete.Move.natural_word_address kind plan valid .order _ ordinalInside]
    exact occupied.order ordinal
  have posLocal : ps.locals.lookup (ofString "pos") = some (.val (.word (BitVec.ofNat 64 (slots.length - 1)))) := bind_lookup_same _ _ _
  have slotRead : eval ps orderRead = some (.val (.word (BitVec.ofNat 64 slot))) := by
    simp only [eval] at orderHeader
    simp [eval, orderRead, localVar, evalHOLExact, evalListHOLExact, toExact, orderHeader, posLocal, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      memLoadHOLExact, isWfShapeExactHOL, orderMapped, orderStored]
  have ssT : ss.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "slot" "t" _ (by decide)).trans psT
  have ssStride : ss.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))) :=
    (bind_lookup_other _ "slot" "stride" _ (by decide)).trans ((bind_lookup_other _ "pos" "stride" _ (by decide)).trans strideLocal)
  have ssSlot : ss.locals.lookup (ofString "slot") = some (.val (.word (BitVec.ofNat 64 slot))) := bind_lookup_same _ _ _
  have keysHeader := MemoryModel.Header.read ss kind plan valid domain _ header ssT 32 (by decide) (by decide) (cell plan .keys 0) (by simp [MemoryModel.headerEntries])
  have args : evalListHOLFinite ss (h := fun address => Classical.propDecidable (ss.memaddrs address)) [localVar "t", keyAddress] = some [.val (.word (cell plan .header 0)), .val (.word query)] := by
    simp only [eval] at keysHeader
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, keyAddress, localVar, ssT, ssSlot, ssStride, keysHeader, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, query]
  have ssModel := MemoryModel.Occupied.of_fields source ss kind plan slots occupied rfl rfl rfl
  have queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64 := slot_fits kind plan valid 0#64 _ slotVector
  have queryMapped : ∀ offset < KeyHash.keySize kind, ss.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)) := by
    intro offset inside
    change source.memaddrs _
    rw [domain]
    exact slot_mapped kind plan valid 0#64 _ slotVector offset inside
  obtain ⟨paid, memory, next, flag, bounded, actual, post, half⟩ := Delete.model_call ss kind plan valid domain little slots room ssModel bits small power header query queryFits queryMapped
    hashCode copyCode memeqCode findCode deleteCode _ args enough
  have slotRun := Input.ScalarScope.declare_execute ps _ "slot" orderRead (BitVec.ofNat 64 slot) deleteCall none slotRead actual
  have posRun := Input.ScalarScope.declare_execute source _ "pos" lastPosition (BitVec.ofNat 64 (slots.length - 1)) (.dec (ofString "slot") .one orderRead deleteCall) none lastRead slotRun
  let canonical := Delete.modelCallState source paid memory
  have restored : restore source "pos" (restore ps "slot" (Delete.modelCallState ss paid memory)) = canonical := by
    change restore source "pos" (restore ps "slot" (bind (bind canonical "pos" (BitVec.ofNat 64 (slots.length - 1))) "slot" (BitVec.ofNat 64 slot))) = canonical
    change restore source "pos" (restore (bind canonical "pos" (BitVec.ofNat 64 (slots.length - 1))) "slot" (bind (bind canonical "pos" (BitVec.ofNat 64 (slots.length - 1))) "slot" (BitVec.ofNat 64 slot))) = canonical
    rw [restore_bound]
    change restore canonical "pos" (bind canonical "pos" (BitVec.ofNat 64 (slots.length - 1))) = canonical
    exact restore_bound _ _ _
  refine ⟨paid, memory, next, flag, bounded, ?_, rfl, post.shape, post.header, ?_, post.footprint⟩
  · simpa only [loopBody, restored] using posRun
  · exact MemoryModel.Occupied.of_fields _ canonical kind plan next post.occupied rfl rfl rfl

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.step_execute
