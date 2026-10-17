import InitECandidate.Solver.GasBudget.U256Eq

namespace InitECandidate.Solver.GasBudget.StorageDebt

noncomputable def debt {α : Type} (zero original current : α) (price : Nat) : Nat:=by
  classical
  exact if original=zero ∧ current≠zero then price else 0
noncomputable def charged {α : Type} (zero original current next : α) (price : Nat) : Nat:=by
  classical
  exact if original=current ∧ current≠next ∧ original=zero then price else 0
noncomputable def refunded {α : Type} (zero original current next : α) (price : Nat) : Nat:=by
  classical
  exact if current≠next ∧ original=next ∧ original=zero then price else 0

/-- Exact storage state-fee algebra under honest original/current/next values.
The original-value and backend/rollback invariants are separate obligations. -/
theorem transition {α : Type} (zero original current next : α) (price : Nat) :
    charged zero original current next price+debt zero original current price=
      refunded zero original current next price+debt zero original next price := by
  classical
  by_cases oz : original=zero
  · subst original
    by_cases cz : current=zero
    · subst current
      by_cases nz : next=zero
      · subst next;simp [charged,refunded,debt]
      · simp [charged,refunded,debt,nz,Ne.symm nz]
    · by_cases nz : next=zero
      · subst next;simp [charged,refunded,debt,cz,Ne.symm cz]
      · simp [charged,refunded,debt,cz,nz,Ne.symm cz,Ne.symm nz]
  · simp [charged,refunded,debt,oz]

structure Entry where
  before : Nat
  after : Nat
  charge : Nat
  refund : Nat

def charges (entries : List Entry) : Nat:=(entries.map Entry.charge).sum
def refunds (entries : List Entry) : Nat:=(entries.map Entry.refund).sum

/-- Drops may destroy a debt without refund; rollback requires its own faithful
projection of the committed trace. This relation does not assume such a trace. -/
inductive Trace : List Entry→Nat→Nat→Prop where
  | nil (amount : Nat) : Trace [] amount amount
  | cons (entry : Entry) (entries : List Entry) (finish : Nat)
      (balanced : entry.refund+entry.after≤entry.charge+entry.before)
      (tail : Trace entries entry.after finish) : Trace (entry::entries) entry.before finish

theorem trace_bound (entries : List Entry) (start finish : Nat) (trace : Trace entries start finish) :
    refunds entries+finish≤charges entries+start := by
  induction trace with
  | nil amount=>simp [charges,refunds]
  | cons entry entries finish balanced tail ih=>
    simp only [charges,refunds,List.map_cons,List.sum_cons] at ih ⊢
    omega

theorem zero_start (entries : List Entry) (finish : Nat) (trace : Trace entries 0 finish) :
    refunds entries≤charges entries := by
  have bound:=trace_bound entries 0 finish trace
  omega

/-- A value transition supplies one balanced ledger entry. -/
theorem transition_entry {α : Type} (zero original current next : α) (price : Nat) :
    let entry : Entry:=⟨debt zero original current price,debt zero original next price,
      charged zero original current next price,refunded zero original current next price⟩
    entry.refund+entry.after≤entry.charge+entry.before := by
  exact Nat.le_of_eq (transition zero original current next price).symm

end InitECandidate.Solver.GasBudget.StorageDebt

#print axioms InitECandidate.Solver.GasBudget.StorageDebt.transition
#print axioms InitECandidate.Solver.GasBudget.StorageDebt.trace_bound
#print axioms InitECandidate.Solver.GasBudget.StorageDebt.zero_start
#print axioms InitECandidate.Solver.GasBudget.StorageDebt.transition_entry
