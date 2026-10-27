import InitECandidate.Solver.Input.CurrentStartup.PayloadWorkspace
import InitECandidate.Solver.Input.PayloadOffsetsTrace

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadValidated
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ current post, ∃ pointer record : BitVec 64, ∃ length : Nat, ∃ returned : ValueHOL 64,
    PayloadWorkspace.Context input current pointer record length ∧
    Guest.GasLimit.le32 input 498 = 540 ∧ Payload.offsetWords input 0 = 540#64 ∧
    (∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (Payload.offsetWords input) position) ∧
    evaluateHOLFiniteState current Payload.offsetContinuation = (some (.returned returned), post)

/-- Whole-main-derived payload execution passes the real four-offset
validator. Its writes retain the original copied bytes and record geometry;
normal return rules out each actual rejection outcome. -/
theorem workspace_reached (input : Guest.InputBlob) (actual : PayloadWorkspace.Reached input) : Reached input := by
  obtain ⟨source, post, pointer, record, length, value, context, actual⟩ := actual
  rcases Payload.offsets_trace source post input pointer 2701132528#64 (BitVec.ofNat 64 length) context.image context.workspace
    context.extra context.txs context.wd context.bal context.domain context.aligned (by decide) (by have := context.room; omega)
    (by decide) (by change 2701132528 + 64 ≤ pointer.toNat; have := context.lower; omega) context.len
    (CanonicalHeader.offset_code source.code context.code) (CanonicalHeader.fail_code source.code context.code) (context.shapes .SszErr)
    (some (.returned value)) actual (by simp) with fault | continued
  · obtain ⟨error, allowed, impossible, paid⟩ := fault
    cases impossible
  · obtain ⟨first, valid, next, paid, bound, funded, nextEq, image, remaining⟩ := continued
    have number := congrArg BitVec.toNat first
    change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 498)).toNat = 540 at number
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Framing.le32_lt input 498; omega)] at number
    have fields : next = {source with memory := next.memory, clock := next.clock} := by rw [nextEq]; rfl
    have nextContext : PayloadWorkspace.Context input next pointer record length := by
      rw [fields] at image ⊢
      exact PayloadWorkspace.Context.memory_clock input source pointer record length next.clock next.memory context image
    exact ⟨next, post, pointer, record, length, value, nextContext, number, first, valid, remaining⟩

theorem separated (input : Guest.InputBlob) (word : BitVec 64) (actual : MainSeparatedInput.StatelessRun input word) : Reached input :=
  workspace_reached input (PayloadWorkspace.separated input word actual)

end InitECandidate.Solver.Input.CurrentStartup.PayloadValidated

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadValidated.workspace_reached
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadValidated.separated
