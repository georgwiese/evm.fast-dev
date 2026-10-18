import InitECandidate.Solver.GasBudget.JournalInitNormal

namespace InitECandidate.Solver.GasBudget.Journal.Initialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (initialized source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + bytes)))) ∧
    (initialized source cursor).globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 capacity))) ∧
    (initialized source cursor).globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 cursor))) ∧
    (initialized source cursor).globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) ∧
    (initialized source cursor).globals.lookup (ofString "ts") = some (.val (.word 0#64)) := by
  have distinct : ([ofString "heap_ptr", ofString "journal_cap", ofString "journal", ofString "journal_n", ofString "ts"] : List MlS).Nodup := by decide
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true, List.nodup_nil] at distinct
  rcases distinct with ⟨⟨hc, hj, hn, ht⟩, ⟨cj, cn, ct⟩, ⟨jn, jt⟩, nt⟩
  simp [initialized, counterState, allocatedState, capState, Input.putGlobal, HolFiniteMapExact.update, FUPDATE,
    Ne.symm ht, Ne.symm hn, Ne.symm hj, Ne.symm ct, Ne.symm cn, Ne.symm cj, Ne.symm jt, Ne.symm jn, Ne.symm nt, hc]

theorem clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (initialized source cursor).clock = source.clock - 1 := rfl

end InitECandidate.Solver.GasBudget.Journal.Initialization

#print axioms InitECandidate.Solver.GasBudget.Journal.Initialization.globals
#print axioms InitECandidate.Solver.GasBudget.Journal.Initialization.clock
