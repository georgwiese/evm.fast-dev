import InitECandidate.Solver.MutableTable.WitnessBuildDictionaryAgreement
import InitECandidate.Solver.WitnessRadix.QueryFunction

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix WitnessRadix.BackingLayout
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

/-- Complete actual original and radix lookup functions return the same
last matching slice from synchronized constructor histories. Both query
pointers may have any alignment, and both executions preserve memory/FFI. -/
theorem paired_dictionary_lookup (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (bits : Nat) (smallBits : bits < 64) (power : plan.capacity = 2^bits)
    (scratch : BitVec 64) (count : Nat) (input : List (Find.Key32 × BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Layout32.Built bits source plan scratch count input logical) (history : History plan input)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (matching : KeysMatch plan keyFor input)
    (records : Records source plan (fun i => sliceFor (BitVec.ofNat 64 i)))
    (table keys vals root leftQuery rightQuery : BitVec 64) (query : ByteKeys.Key)
    (represented : QueryMemory.Represents right table keys vals root
      (buildIndex ByteKeys.bit 256 (OrdinalTree.entries keyFor sliceFor (ordinals input.length))))
    (rootMapped : right.memaddrs (table + 24#64)) (rootWord : right.memory (table + 24#64) = .word root)
    (leftView : MemoryBytes.ByteView source leftQuery query) (rightView : MemoryBytes.ByteView right rightQuery query)
    (leftFits : leftQuery.toNat + 32 < 2^64) (rightFits : rightQuery.toNat + 32 < 2^64)
    (leftLittle : source.be = false) (rightLittle : right.be = false)
    (leftDb : source.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 plan.table))))
    (leftHash : source.locals.lookup (ofString "hash") = some (.val (.word leftQuery)))
    (rightDb : right.locals.lookup (ofString "db") = some (.val (.word table)))
    (rightHash : right.locals.lookup (ofString "hash") = some (.val (.word rightQuery)))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (leftMemeq : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (findCode : source.code.lookup (ofString "htab_find_slot") = some (Find.formals, Find.body, .one))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (rightMemeq : right.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (leftClock : 6 * input.length + 3 ≤ source.clock) (rightClock : 262 ≤ right.clock) :
    ∃ leftPaid rightPaid, leftPaid ≤ 6 * input.length + 3 ∧ rightPaid ≤ 262 ∧
      (evaluateHOLFiniteState source NodeDb.body).1 =
        (evaluateHOLFiniteState right QueryEmpty.body).1 ∧
      (evaluateHOLFiniteState right QueryEmpty.body).1 = some (.returned (QueryExecution.valueOf
        (lastValue query (OrdinalTree.entries keyFor sliceFor (ordinals input.length))))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source NodeDb.body).2 =
        emptyLocalsHOLFinite { source with clock := source.clock - leftPaid } ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState right QueryEmpty.body).2 =
        emptyLocalsHOLFinite { right with clock := right.clock - rightPaid } := by
  obtain ⟨leftPaid, leftTarget, leftBound, leftRun, leftFrame⟩ :=
    dictionary_lookup source plan ready domain bits smallBits power scratch count input logical built history _ records
      leftQuery query leftView leftFits leftLittle leftDb leftHash hashCode leftMemeq findCode getCode leftClock
  obtain ⟨rightPaid, rightBound, rightAnswer, rightFrame⟩ :=
    QueryExecution.lookup_built _ right table keys vals rightQuery root query represented rootMapped rootWord
      rightDb rightHash rightMemeq rightView rightFits rightLittle rightClock
  have leftAnswer := congrArg Prod.fst leftRun
  rw [dictionary_last_agrees plan ready keyFor sliceFor input matching (History.length_bound plan input history) query] at leftAnswer
  refine ⟨leftPaid, rightPaid, leftBound, rightBound, leftAnswer.trans rightAnswer.symm, rightAnswer, ?_, rightFrame⟩
  rw [leftRun]
  exact leftFrame

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.paired_dictionary_lookup
