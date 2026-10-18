import InitECandidate.Solver.MutableTable.TruncateLoop
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Actual non-timeout truncate tail, with no entry-clock budget premise.
Add-clock equality funds the internal constructive proof, then removes the
padding. The result is derived to be return0, with the exact remaining count. -/
theorem tail_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots)
    (bits : Nat) (small : bits < 64) (power : plan.capacity = 2 ^ bits)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (limit : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (strideLocal : source.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 (stride kind)))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (memeqCode : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (result : Option (PanSemResultExact 64)) (notTimeout : result ≠ some .timeOut)
    (normal : evaluateHOLFiniteState source tail = (result, target)) :
    ∃ paid memory next, paid + price kind (min slots.length limit.toNat) ≤ price kind slots.length ∧ paid ≤ source.clock ∧ result = some (.returned (.val (.word 0#64))) ∧
      ModelPost source kind plan slots.length limit paid memory target next := by
  let extra := price kind slots.length
  let paddedSource := {source with clock := source.clock + extra}
  let paddedTarget := {target with clock := target.clock + extra}
  have lifted := panPropsEvaluateAddClockEq tail source result target extra ⟨normal, notTimeout⟩
  have paddedModel := MemoryModel.Occupied.of_fields source paddedSource kind plan slots occupied rfl rfl rfl
  obtain ⟨paid, memory, next, bounded, resultEq, post⟩ := tail_non_timeout kind plan valid bits small power limit result notTimeout slots.length paddedSource paddedTarget
    domain little slots rfl room paddedModel header tableLocal strideLocal limitLocal hashCode copyCode memeqCode findCode deleteCode
    (by change price kind slots.length ≤ source.clock + extra; omega) lifted
  have stripped := InitECandidate.Solver.strip_clock_padding source target {source with memory := memory} paid extra (by omega) post.frame
  refine ⟨paid, memory, next, bounded, stripped.1, resultEq, stripped.2, post.length, post.header, ?_, post.footprint⟩
  exact MemoryModel.Occupied.of_fields paddedTarget target kind plan next post.occupied rfl rfl rfl

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.tail_bound
