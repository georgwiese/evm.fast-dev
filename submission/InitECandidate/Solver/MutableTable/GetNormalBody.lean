import InitECandidate.Solver.MutableTable.GetNormalOrigin
import InitECandidate.Solver.MutableTable.GetModelExecution
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original getter return derives its physical result pair, clock
price and complete nonlocal read-only frame without an entry allowance. -/
theorem model_body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    ∃ paid flag value, paid ≤ bodyPrice kind slots.length ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      returned = pair flag value ∧ emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  obtain ⟨paid,flag,value,price,funded,binary,origin,returnedEq,frame⟩ := model_body_normal_origin source target kind plan slots cursor floor table environment query queryFits queryMapped tableLocal keyLocal returned normal
  exact ⟨paid,flag,value,price,funded,binary,returnedEq,frame⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_body_normal
