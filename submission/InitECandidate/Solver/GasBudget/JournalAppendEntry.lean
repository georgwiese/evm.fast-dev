import InitECandidate.Solver.GasBudget.JournalAppendProgram

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The real jset getter and overflow guard derive room for one journal
record from original normal execution. The old flag/value are actual getter
results; the counter/cap have survived its complete read-only frame. -/
theorem set_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : NaturalLayout.Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : WarmKeys.Environment source) (query count cap : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (NaturalLayout.cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word cap)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source setBody = (some (.returned returned), post)) :
    count.toNat < cap.toNat ∧ ∃ paid flag value finish,
      1 ≤ paid ∧ paid ≤ Get.bodyPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧ (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "old") (Get.pair flag value) {source with clock := source.clock - paid}) setAfterGuard = (some (.returned returned), finish) ∧
      post = restore source "old" finish := by
  rw [set_shape] at normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t", localVar "key"] =
      some [.val (.word (NaturalLayout.cell plan .header 0)), .val (.word query)] := by
    simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, tableLocal, keyLocal]
  obtain ⟨paid, flag, value, finish, positive, bounded, fits, binary, suffixRun, frame⟩ :=
    Get.model_normal_entry source post kind plan slots cursor floor table environment query queryFits queryMapped getCode "old" _ _ args returned normal
  let ready := setVarHOLFinite (ofString "old") (Get.pair flag value) {source with clock := source.clock - paid}
  obtain ⟨room, afterGuard⟩ := guard_normal ready finish count cap 4#64 counter capacity environment.trapCode setAfterGuard returned suffixRun
  exact ⟨room, paid, flag, value, finish, positive, bounded, fits, binary, afterGuard, frame⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_guard_normal
