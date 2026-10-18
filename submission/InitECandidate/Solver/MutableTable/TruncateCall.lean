import InitECandidate.Solver.MutableTable.TruncateExecution
import InitECandidate.Solver.Input.IgnoredCallNormal

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Real original ignored-result truncate caller on a successful actual
run, with no caller-clock allowance or logical self-lookup premise. Only
the removed population is charged; the original layout is retained. -/
theorem call_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (limit : BitVec 64)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (truncateCode : source.code.lookup (ofString "htab_truncate") = some (formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (ReadCall.values (cell plan .header 0) limit))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_truncate") arguments) = (none, target)) :
    ∃ paid memory next, paid + price kind (min slots.length limit.toNat) ≤ price kind slots.length + 1 ∧ paid ≤ source.clock ∧
      ModelPost source kind plan slots.length limit paid memory target next := by
  obtain ⟨callee, called, tableLocal, limitLocal⟩ := ReadCall.environment source.code.lookup (ofString "htab_truncate") body .one "n" (by decide) (cell plan .header 0) limit truncateCode
  obtain ⟨positive, bodyTarget, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "htab_truncate") arguments _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, next, bounded, fits, resultEq, post⟩ := execute_bound entry bodyTarget kind plan valid domain little slots room entryModel bits small power header limit tableLocal limitLocal
    hashCode copyCode memeqCode findCode deleteCode (some (.returned returned)) (by intro impossible; cases impossible) bodyRun
  have returnedEq : returned = .val (.word 0#64) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  subst returned
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "htab_truncate") arguments _ body callee .one (.val (.word 0#64)) bodyTarget args called (by omega) bodyRun (by simp [shapeOfHOLExact, shapeEqHOL])
  have targetEq := congrArg Prod.snd (normal.symm.trans actual)
  change target = {bodyTarget with locals := source.locals} at targetEq
  refine ⟨paid + 1, memory, next, by omega, ?_, ?_, post.length, post.header, ?_, post.footprint⟩
  · change paid ≤ source.clock - 1 at fits
    omega
  · rw [targetEq]
    change emptyLocalsHOLFinite bodyTarget = _
    rw [post.frame]
    change emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - 1 - paid} = _
    have subtract : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
    rw [subtract]
  · rw [targetEq]
    exact MemoryModel.Occupied.of_fields bodyTarget _ kind plan next post.occupied rfl rfl rfl

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.call_bound
