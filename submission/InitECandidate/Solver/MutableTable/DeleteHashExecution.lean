import InitECandidate.Solver.MutableTable.DeleteAfterHash

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original hash caller and its complete optional movement
continuation. Scoped hash/home/movable bindings restore, while the hole is
unchanged or becomes the current scan slot. All old used bytes remain intact. -/
theorem hash_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved ≠ deleted)
    (locals : Move.Locals source kind plan hole (entries moved)) (value : BitVec 64)
    (valueCell : source.memory (cell plan .values (8 * entries moved)) = .word value)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock) :
    ∃ paid memory nextEntries nextHole, paid ≤ KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ∧
      evaluateHOLFiniteState source hashCall = (none, WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) ∧
      (nextHole = hole ∨ nextHole = entries moved) ∧
      Pending (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - paid} "i" (BitVec.ofNat 64 nextHole)) kind plan count deleted nextEntries nextHole ∧
      MemoryModel.Header memory kind plan (BitVec.ofNat 64 count) ∧
      (∀ query < plan.capacity, Find.usedByte {source with memory := memory} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
        Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query)) := by
  let pointer := cell plan .keys 0 + BitVec.ofNat 64 (entries moved) * BitVec.ofNat 64 (stride kind)
  have inside := pending.inside moved active
  have vectorInside : (BitVec.ofNat 64 (entries moved)).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans inside (capacity_small kind plan valid))]
    exact inside
  have fits : pointer.toNat + KeyHash.keySize kind < 2 ^ 64 := slot_fits kind plan valid 0#64 _ vectorInside
  have mappedKey : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset)) := by
    intro offset byteInside
    rw [domain]
    exact slot_mapped kind plan valid 0#64 _ vectorInside offset byteInside
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [keyAddress "j", localVar "klen"] = some (KeyHash.values kind pointer) := by
    simp [KeyHash.values, keyAddress, scaled, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, pointer,
      locals.keys, locals.stride, locals.slot, locals.length, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
  obtain ⟨hash, hashRun⟩ := KeyHash.call_of_mapped source kind pointer "h" [keyAddress "j", localVar "klen"] afterHash args hashCode fits mappedKey little (by omega)
  let entered := WitnessRadix.QueryBranch.bind {source with clock := source.clock - KeyHash.hashPrice kind} "h" hash
  have enteredLocals : Move.Locals entered kind plan hole (entries moved) :=
    ⟨(bind_lookup_other _ "h" "keys" _ (by decide)).trans locals.keys,
      (bind_lookup_other _ "h" "vals" _ (by decide)).trans locals.values,
      (bind_lookup_other _ "h" "order" _ (by decide)).trans locals.order,
      (bind_lookup_other _ "h" "order_pos" _ (by decide)).trans locals.position,
      (bind_lookup_other _ "h" "klen" _ (by decide)).trans locals.length,
      (bind_lookup_other _ "h" "stride" _ (by decide)).trans locals.stride,
      (bind_lookup_other _ "h" "i" _ (by decide)).trans locals.hole,
      (bind_lookup_other _ "h" "j" _ (by decide)).trans locals.slot⟩
  have enteredPending := Pending.of_fields source entered kind plan count deleted entries hole pending rfl rfl rfl
  obtain ⟨tailPaid, memory, nextEntries, nextHole, bounded, tailRun, choice, nextPending, nextHeader, usedStable⟩ := after_hash_execute entered kind plan valid domain count deleted entries hole enteredPending moved active enteredLocals value hash valueCell header
    (bind_lookup_same _ _ _) ((bind_lookup_other _ "h" "cap" _ (by decide)).trans capLocal) copyCode
    (by change MemeqByteRuntime.price (KeyHash.keySize kind) + 1 ≤ source.clock - KeyHash.hashPrice kind; omega)
  rw [tailRun] at hashRun
  let canonical := {source with memory := memory, clock := source.clock - (KeyHash.hashPrice kind + tailPaid)}
  have subtract : source.clock - KeyHash.hashPrice kind - tailPaid = source.clock - (KeyHash.hashPrice kind + tailPaid) := by omega
  have targetEq : WitnessRadix.QueryBranch.bind {entered with memory := memory, clock := entered.clock - tailPaid} "i" (BitVec.ofNat 64 nextHole) =
      WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind canonical "h" hash) "i" (BitVec.ofNat 64 nextHole) := by
    change WitnessRadix.QueryBranch.bind (WitnessRadix.QueryBranch.bind {source with memory := memory, clock := source.clock - KeyHash.hashPrice kind - tailPaid} "h" hash) "i" _ = _
    rw [subtract]
  have restored : restore source "h" (WitnessRadix.QueryBranch.bind {entered with memory := memory, clock := entered.clock - tailPaid} "i" (BitVec.ofNat 64 nextHole)) =
      WitnessRadix.QueryBranch.bind canonical "i" (BitVec.ofNat 64 nextHole) := by
    rw [targetEq, restore_bind_other source (WitnessRadix.QueryBranch.bind canonical "h" hash) "h" "i" _ (by decide)]
    change WitnessRadix.QueryBranch.bind (restore canonical "h" (WitnessRadix.QueryBranch.bind canonical "h" hash)) "i" _ = _
    rw [restore_bound]
  refine ⟨KeyHash.hashPrice kind + tailPaid, memory, nextEntries, nextHole, by omega, ?_, choice, ?_, nextHeader, usedStable⟩
  · simpa only [hashCall, restored] using hashRun
  · exact Pending.of_fields _ _ kind plan count deleted nextEntries nextHole nextPending rfl rfl rfl

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.hash_execute
