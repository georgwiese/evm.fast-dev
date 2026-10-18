import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def currentCount (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  match source.globals.lookup (ofString "journal_n") with
  | some (.val (.word word)) => word.toNat
  | _ => 0

theorem currentCount_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (small : count < 2 ^ 64)
    (read : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count)))) :
    currentCount source = count := by
  simp only [currentCount, read, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-- Counter conservation for actual states. Appends create records; rollback
consumes them; a new transaction discards the still-live suffix. -/
def CounterEffect (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (appended restored discarded : Nat) : Prop :=
  currentCount target + restored + discarded = currentCount source + appended

theorem CounterEffect.unchanged (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : target.globals.lookup (ofString "journal_n") = source.globals.lookup (ofString "journal_n")) :
    CounterEffect source target 0 0 0 := by simp [CounterEffect, currentCount, same]

theorem CounterEffect.append (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat)
    (small : count + 1 < 2 ^ 64)
    (before : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (after : target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1))))) :
    CounterEffect source target 1 0 0 := by
  unfold CounterEffect
  rw [currentCount_read source count (by omega) before, currentCount_read target (count + 1) small after]

theorem CounterEffect.restore (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (count snap : Nat)
    (small : count < 2 ^ 64)
    (before : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (after : target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (min count snap))))) :
    CounterEffect source target 0 (count - snap) 0 := by
  unfold CounterEffect
  rw [currentCount_read source count small before, currentCount_read target (min count snap) (by omega) after]
  omega

theorem CounterEffect.reset (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (after : target.globals.lookup (ofString "journal_n") = some (.val (.word 0#64))) :
    CounterEffect source target 0 0 (currentCount source) := by
  unfold CounterEffect
  rw [currentCount_read target 0 (by decide) after]
  omega

theorem CounterEffect.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {a₁ r₁ d₁ a₂ r₂ d₂ : Nat} (first : CounterEffect source middle a₁ r₁ d₁) (second : CounterEffect middle target a₂ r₂ d₂) :
    CounterEffect source target (a₁ + a₂) (r₁ + r₂) (d₁ + d₂) := by
  unfold CounterEffect at *
  omega

structure CounterLedger (initial : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) where
  appended : Nat
  restored : Nat
  discarded : Nat
  balance : currentCount source + restored + discarded = initial + appended

def CounterLedger.start (source : PanSemStateFiniteExact 64 Guest.HostMemory) : CounterLedger (currentCount source) source :=
  ⟨0, 0, 0, by omega⟩

def CounterLedger.advance {initial : Nat} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (ledger : CounterLedger initial source) (a r d : Nat) (effect : CounterEffect source target a r d) : CounterLedger initial target :=
  ⟨ledger.appended + a, ledger.restored + r, ledger.discarded + d, by
    have balance := ledger.balance
    unfold CounterEffect at effect
    omega⟩

/-- The bound applies to every accounted prefix, across any number of
snapshots, restores and transaction resets. Whole-program construction of
this ledger and the number of appends remain separate proof obligations. -/
theorem CounterLedger.restored_le {initial : Nat} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (ledger : CounterLedger initial source) : ledger.restored ≤ initial + ledger.appended := by
  have balance := ledger.balance
  omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.currentCount_read
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterEffect.unchanged
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterEffect.append
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterEffect.restore
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterEffect.reset
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterEffect.trans
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterLedger.start
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterLedger.advance
#print axioms InitECandidate.Solver.GasBudget.Journal.CounterLedger.restored_le
