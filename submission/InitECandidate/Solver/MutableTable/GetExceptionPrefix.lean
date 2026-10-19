import InitECandidate.Solver.MutableTable.GetExceptionOrigin
import InitECandidate.Solver.MutableTable.GetNoException
import InitECandidate.Solver.Input.ScopedCallException
import InitECandidate.Solver.Input.BinaryCallData

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem model_exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (formals, body, pairShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) pairShape (ofString "htab_get") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ paid flag value inner, 1 ≤ paid ∧ paid ≤ bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (pair flag value) {source with clock := source.clock - paid}) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨paid, flag, value, inner, positive, bounded, funded, binary, _, tailRun, scope⟩ :=
    model_exception_prefix_origin source post kind plan slots cursor floor table environment query queryFits queryMapped
      getCode name arguments continuation args identifier payload run
  exact ⟨paid, flag, value, inner, positive, bounded, funded, binary, tailRun, scope⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_exception_prefix
