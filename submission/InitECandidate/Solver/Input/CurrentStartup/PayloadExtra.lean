import InitECandidate.Solver.Input.CurrentStartup.PayloadValidated
import InitECandidate.Solver.Input.PayloadExtraGuard

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadExtra
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ current post, ∃ pointer record : BitVec 64, ∃ length : Nat, ∃ returned : ValueHOL 64,
    PayloadWorkspace.Context input current pointer record length ∧
    Payload.offsetWords input 0 = 540#64 ∧
    (∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (Payload.offsetWords input) position) ∧
    (Payload.offsetWords input 1).toNat - 540 ≤ 32 ∧
    evaluateHOLFiniteState current Payload.afterExtra = (some (.returned returned), post) ∧
    PayloadEntry.Endpoint input post pointer length returned

/-- Real payload return passes the actual extra-data guard, deriving its
32-byte bound at the original state and clock. -/
theorem validated (input : Guest.InputBlob) (actual : PayloadValidated.Reached input) : Reached input := by
  obtain ⟨source, post, pointer, record, length, value, context, raw, first, valid, actual, endpoint⟩ := actual
  have extraCell : source.locals.lookup (ofString "o_extra") = some (.val (.word 540#64)) := by rw [context.extra, first]
  have lower : 540 ≤ (Payload.offsetWords input 1).toNat := (valid 1 (by decide)).1
  have read := Payload.extra_test_read source input extraCell context.txs lower
  rw [Payload.extra_shape] at actual
  obtain ⟨small, after⟩ := guard_actual source post Payload.extraTest 51#64 (32 < (Payload.offsetWords input 1).toNat - 540) read
    (CanonicalHeader.fail_code source.code context.code) (context.shapes .SszErr) Payload.afterExtra value actual
  exact ⟨source, post, pointer, record, length, value, context, first, valid, (by omega), after, endpoint⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  validated input (PayloadValidated.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.PayloadExtra

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadExtra.validated
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadExtra.separated
