import InitECandidate.Solver.MutableTable.GetModelOrigin
import InitECandidate.Solver.MutableTable.GetGeneralExecution
import InitECandidate.Solver.MutableTable.TableState
import InitECandidate.Solver.MutableTable.MemoryModelEntry
import InitECandidate.Solver.GasBudget.WarmKeysInvariant

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def bodyPrice (kind : KeyHash.Kind) (count : Nat) : Nat :=
  Find.generalProbePrice kind * count + (KeyHash.hashPrice kind + 1)

/-- Current physical table ownership supplies every original getter read,
including arbitrary stored value words and all collision probes. -/
theorem model_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (enough : bodyPrice kind slots.length ≤ source.clock) :
    ∃ paid flag value target, paid ≤ bodyPrice kind slots.length ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState source body = (some (.returned (pair flag value)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  obtain ⟨paid,flag,value,target,price,binary,origin,run,frame⟩ := model_execute_origin source kind plan slots cursor floor table environment query queryFits queryMapped tableLocal keyLocal enough
  exact ⟨paid,flag,value,target,price,binary,run,frame⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_execute
