import InitECandidate.Solver.MutableTable.DeleteNormalCallValues

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Actual original deletion caller with no source-clock allowance. The
current owned physical table supplies room/power bounds; actual non-timeout
clock equality removes temporary funding and retains the full ownership post. -/
theorem model_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor) (environment : GasBudget.WarmKeys.Environment source)
    (query : BitVec 64) (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ paid memory next flag, paid ≤ modelPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧
      target = modelCallState source paid memory ∧ ModelPost source kind plan slots paid memory target next flag ∧ 2 * next.length ≤ plan.capacity := by
  obtain ⟨paid,memory,next,flag,bounded,fits,frame,post,half,nextValues⟩ :=
    model_call_normal_values source target kind plan slots cursor floor table environment query queryFits queryMapped deleteCode arguments args (fun _=>True) (fun _ _ _ _ _=>True.intro) normal
  exact ⟨paid,memory,next,flag,bounded,fits,frame,post,half⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_call_normal
