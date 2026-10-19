import InitECandidate.Solver.GasBudget.JournalDeleteGuardValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- jdel either returns from its actual absent-key branch without appending,
or derives room from the real overflow guard before the append suffix. -/
theorem delete_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : NaturalLayout.Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : WarmKeys.Environment source) (query count cap : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (NaturalLayout.cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word cap)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source deleteBody = (some (.returned returned), post)) :
    (∃ paid, 1 ≤ paid ∧ paid ≤ Get.bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧
      returned = .val (.word 0#64) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - paid}) ∨
    (count.toNat < cap.toNat ∧ ∃ paid value finish,
      1 ≤ paid ∧ paid ≤ Get.bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "old") (Get.pair 1#64 value) {source with clock := source.clock - paid}) deleteAfterGuard = (some (.returned returned), finish) ∧
      post = restore source "old" finish) := by
  have branches := delete_guard_normal_values source post kind plan slots cursor floor table environment query count cap
    (fun _=>True) (fun _ _ _ _ _=>True.intro) queryFits queryMapped tableLocal keyLocal getCode counter capacity returned normal
  rcases branches with absent | present
  · exact Or.inl absent
  · obtain ⟨room,paid,value,finish,positive,bounded,funded,owned,run,restored⟩ := present
    exact Or.inr ⟨room,paid,value,finish,positive,bounded,funded,run,restored⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.empty_read
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_guard_normal
