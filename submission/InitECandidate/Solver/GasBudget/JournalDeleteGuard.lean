import InitECandidate.Solver.GasBudget.JournalAppendEntry

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

theorem empty_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag value : BitVec 64)
    (old : source.locals.lookup (ofString "old") = some (Get.pair flag value)) :
    eval source emptyCondition = some (.val (.word (if flag = 0#64 then 1#64 else 0#64))) := by
  simp [eval, emptyCondition, localVar, evalHOLExact, toExact, old, Get.pair,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

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
  rw [delete_shape] at normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t", localVar "key"] =
      some [.val (.word (NaturalLayout.cell plan .header 0)), .val (.word query)] := by
    simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, tableLocal, keyLocal]
  obtain ⟨paid, flag, value, finish, positive, bounded, fits, binary, suffixRun, frame⟩ :=
    Get.model_normal_entry source post kind plan slots cursor floor table environment query queryFits queryMapped getCode "old" _ _ args returned normal
  let ready := setVarHOLFinite (ofString "old") (Get.pair flag value) {source with clock := source.clock - paid}
  have old : ready.locals.lookup (ofString "old") = some (Get.pair flag value) := by simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have test := empty_read ready flag value old
  simp only [eval] at test
  by_cases absent : flag = 0#64
  · rw [if_pos absent] at test
    have choose : evaluateHOLFiniteState ready emptyCheck = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite ready) := by
      rw [emptyCheck, evaluateHOLFiniteState_ite, test]
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    rw [evaluateHOLFiniteState_seq_line780, choose] at suffixRun
    have returnEq : returned = .val (.word 0#64) := by
      simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using (congrArg Prod.fst suffixRun).symm
    have finishEq := congrArg Prod.snd suffixRun
    change emptyLocalsHOLFinite ready = finish at finishEq
    left
    refine ⟨paid, positive, bounded, fits, returnEq, ?_⟩
    rw [frame, ← finishEq]
    rfl
  · have present : flag = 1#64 := binary.resolve_left absent
    rw [if_neg absent] at test
    have choose : evaluateHOLFiniteState ready emptyCheck = (none, ready) := by
      rw [emptyCheck, evaluateHOLFiniteState_ite, test]
      simp [evaluateHOLFiniteState_skip]
    rw [WitnessRadix.StateSteps.next_sequence ready ready _ _ choose (Nat.le_refl _)] at suffixRun
    obtain ⟨room, afterGuard⟩ := guard_normal ready finish count cap 5#64 counter capacity environment.trapCode deleteAfterGuard returned suffixRun
    right
    refine ⟨room, paid, value, finish, positive, bounded, fits, ?_, ?_⟩
    · simpa only [ready, present] using afterGuard
    · exact frame

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.empty_read
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_guard_normal
