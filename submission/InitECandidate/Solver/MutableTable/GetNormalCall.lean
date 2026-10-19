import InitECandidate.Solver.MutableTable.GetCallOrigin
import InitECandidate.Solver.MutableTable.GetNormalBody
import InitECandidate.Solver.MutableTable.GetCall32
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original getter declaration resumes with its binary flag and
actual stored word, preserving every nonlocal field except the paid clock.
The enclosing normal execution derives funding and the real callee result. -/
theorem model_normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_get") arguments continuation) = (some (.returned returned), post)) :
    ∃ paid flag value finish, 1 ≤ paid ∧ paid ≤ bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - paid}) continuation = (some (.returned returned), finish) ∧
      post = restore source name finish := by
  obtain ⟨paid,flag,value,finish,positive,price,funded,binary,origin,run,frame⟩ := model_normal_entry_origin source post kind plan slots cursor floor table environment query queryFits queryMapped
    getCode name arguments continuation args returned normal
  exact ⟨paid,flag,value,finish,positive,price,funded,binary,run,frame⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_normal_entry
