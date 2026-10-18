import InitECandidate.Solver.MutableTable.TruncateTailBound

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole unchanged truncate body on any non-timeout execution, without
an entry-clock bound or a self-lookup success premise. The actual result is
derived to be return0, and only the removed population is charged. -/
theorem execute_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (limit : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (result : Option (PanSemResultExact 64)) (notTimeout : result ≠ some .timeOut)
    (normal : evaluateHOLFiniteState source body = (result, target)) :
    ∃ paid memory next, paid + price kind (min slots.length limit.toNat) ≤ price kind slots.length ∧ paid ≤ source.clock ∧
      result = some (.returned (.val (.word 0#64))) ∧ ModelPost source kind plan slots.length limit paid memory target next := by
  let entered := bind source "stride" (BitVec.ofNat 64 (stride kind))
  let output := evaluateHOLFiniteState entered tail
  have read := MemoryModel.Header.read source kind plan valid domain _ header tableLocal 8 (by decide) (by decide) (BitVec.ofNat 64 (stride kind)) (by simp [MemoryModel.headerEntries])
  have scopeRun := Input.ScalarScope.declare_execute source output.2 "stride" (Find.tableLoad 8#64) (BitVec.ofNat 64 (stride kind)) tail output.1 read (by rfl)
  have whole : evaluateHOLFiniteState source body = (output.1, restore source "stride" output.2) := by
    rw [body_shape]
    exact scopeRun
  have resultEq := congrArg Prod.fst (whole.symm.trans normal)
  have targetEq := congrArg Prod.snd (normal.symm.trans whole)
  change output.1 = result at resultEq
  change target = restore source "stride" output.2 at targetEq
  have tailRun : evaluateHOLFiniteState entered tail = (result, output.2) := Prod.ext resultEq rfl
  have entryModel := MemoryModel.Occupied.of_fields source entered kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, next, bounded, fits, actualResult, post⟩ := tail_bound entered output.2 kind plan valid domain little slots room entryModel bits small power header limit
    ((bind_lookup_other _ "stride" "t" _ (by decide)).trans tableLocal) (bind_lookup_same _ _ _)
    ((bind_lookup_other _ "stride" "n" _ (by decide)).trans limitLocal) hashCode copyCode memeqCode findCode deleteCode result notTimeout tailRun
  refine ⟨paid, memory, next, bounded, fits, actualResult, ?_, post.length, post.header, ?_, post.footprint⟩
  · rw [targetEq]
    exact post.frame
  · rw [targetEq]
    exact MemoryModel.Occupied.of_fields output.2 _ kind plan next post.occupied rfl rfl rfl

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.execute_bound
