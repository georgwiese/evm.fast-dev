import InitECandidate.Solver.MutableTable.GetAssignedOrigin
import InitECandidate.Solver.MutableTable.GetNormalCall
import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.BinaryCallData

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original getter also appears as assignment to an existing pair.
The actual normal caller supplies the real callee execution and shape checks. -/
theorem model_assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor) (environment : GasBudget.WarmKeys.Environment source)
    (query : BitVec 64) (queryFits : query.toNat + KeyHash.keySize kind < 2^64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : MlS) (arguments : List (ExpHOL 64))
    (expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word (cell plan .header 0)), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local, name), none)) (ofString "htab_get") arguments) = (none, post)) :
    ∃ paid flag value, 1 ≤ paid ∧ paid ≤ bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧
      (flag = 0#64 ∨ flag = 1#64) ∧
      post = setVarHOLFinite name (pair flag value) {source with clock := source.clock - paid} := by
  obtain ⟨paid,flag,value,positive,price,funded,binary,origin,postEq⟩ := model_assigned_origin source post kind plan slots cursor floor table environment query queryFits queryMapped getCode name arguments expectedArgs normal
  exact ⟨paid,flag,value,positive,price,funded,binary,postEq⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_assigned_normal
