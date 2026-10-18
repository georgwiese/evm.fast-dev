import InitECandidate.Solver.GasBudget.RecipientProgram
import InitECandidate.Solver.GasBudget.MessageScalar

namespace InitECandidate.Solver.GasBudget.Recipient
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable NaturalLayout

def linkedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (aa ak : BitVec 64) :=
  MessageField.putState (MessageField.putState source start 152 aa) start 160 ak

/-- Execute the actual final stores of both warm-table pointers and reach
the real process_message_call declaration without consuming source clock. -/
theorem links_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (aa ak : BitVec 64)
    (region : MemoryRegion.Valid ⟨start, 176⟩) (domain : source.memaddrs = InitE.ordinaryDomain)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))))
    (aaLocal : source.locals.lookup (ofString "aa") = some (.val (.word aa)))
    (akLocal : source.locals.lookup (ofString "ak") = some (.val (.word ak))) :
    evaluateHOLFiniteState source afterRecipient = evaluateHOLFiniteState (linkedState source start aa ak) messageSite := by
  let first := MessageField.putState source start 152 aa
  let last := linkedState source start aa ak
  have aaRead : eval source (localVar "aa") = some (.val (.word aa)) := by
    simpa only [eval, localVar, evalHOLExact, toExact] using aaLocal
  have akRead : eval first (localVar "ak") = some (.val (.word ak)) := by
    simpa only [eval, localVar, evalHOLExact, toExact, first, MessageField.putState] using akLocal
  have firstRun := MessageField.scalar_execute source start 152 aa (localVar "aa") region (by decide) (by decide) domain messageLocal aaRead
  have lastRun := MessageField.scalar_execute first start 160 ak (localVar "ak") region (by decide) (by decide) domain messageLocal akRead
  rw [after_recipient_shape,
    StateSteps.next_sequence source source .skip _ (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _),
    StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    StateSteps.next_sequence first last _ _ lastRun (Nat.le_refl _)]

theorem linked_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor start : Nat) (aa ak : BitVec 64)
    (table : TableState source kind plan slots cursor floor) (region : MemoryRegion.Valid ⟨start, 176⟩)
    (later : ∀ pool, start + 176 ≤ plan.base pool) :
    TableState (linkedState source start aa ak) kind plan slots cursor floor := by
  exact MessageField.scalar_table _ kind plan slots cursor floor start 160 ak
    (MessageField.scalar_table source kind plan slots cursor floor start 152 aa table region (by decide) later) region (by decide) later

theorem linked_gas (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (aa ak : BitVec 64) :
    (linkedState source start aa ak).memory (BitVec.ofNat 64 start + 40#64) = source.memory (BitVec.ofNat 64 start + 40#64) := by
  exact (MessageField.scalar_other _ start 160 40 ak (by decide) (by decide) (by decide)).trans
    (MessageField.scalar_other source start 152 40 aa (by decide) (by decide) (by decide))

theorem linked_pointers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (aa ak : BitVec 64) :
    (linkedState source start aa ak).memory (BitVec.ofNat 64 start + 152#64) = .word aa ∧
    (linkedState source start aa ak).memory (BitVec.ofNat 64 start + 160#64) = .word ak := by
  constructor
  · rw [show (linkedState source start aa ak).memory (BitVec.ofNat 64 start + 152#64) =
        (MessageField.putState source start 152 aa).memory (BitVec.ofNat 64 start + 152#64) from
        MessageField.scalar_other _ start 160 152 ak (by decide) (by decide) (by decide)]
    simp [MessageField.putState, StoreWord.put]
  · simp [linkedState, MessageField.putState, StoreWord.put]

theorem linked_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (aa ak query : BitVec 64)
    (region : MemoryRegion.Valid ⟨start, 176⟩) (outside : query.toNat < start ∨ start + 176 ≤ query.toNat) :
    (linkedState source start aa ak).memory query = source.memory query := by
  exact (MessageField.scalar_outside _ start 160 ak query region (by decide) outside).trans
    (MessageField.scalar_outside source start 152 aa query region (by decide) outside)

end InitECandidate.Solver.GasBudget.Recipient

#print axioms InitECandidate.Solver.GasBudget.Recipient.links_execute
#print axioms InitECandidate.Solver.GasBudget.Recipient.linked_table
#print axioms InitECandidate.Solver.GasBudget.Recipient.linked_gas
#print axioms InitECandidate.Solver.GasBudget.Recipient.linked_pointers
#print axioms InitECandidate.Solver.GasBudget.Recipient.linked_outside
