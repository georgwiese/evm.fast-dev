import InitECandidate.Solver.GasBudget.JournalProgram
import InitECandidate.Solver.MutableTable.FamilyControl

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (snap count : BitVec 64)
    (snapshot : source.locals.lookup (ofString "snap") = some (.val (.word snap)))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    eval source condition = some (.val (.word (if snap.toNat < count.toNat then 1#64 else 0#64))) := by
  change eval source condition = some (.val (.word (if snap < count then 1#64 else 0#64)))
  simp [eval, condition, countVar, localVar, evalHOLExact, toExact, snapshot, counter,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem decrement_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word count))) :
    evaluateHOLFiniteState source decrement = (none, Input.putGlobal source "journal_n" (count - 1#64)) := by
  apply Input.global_assign_execute source "journal_n" count (count - 1#64) _ counter
  simp [eval, countVar, evalHOLExact, evalListHOLExact, toExact, counter, valueIsWord, valueWord, wordOpHOL, wordOp]

/-- The unsigned guard excludes wraparound on the actual decrement, even
when the snapshot or counter has its high bit set. -/
theorem decrement_progress (snap count : BitVec 64) (active : snap.toNat < count.toNat) :
    (count - 1#64).toNat = count.toNat - 1 ∧
      snap.toNat ≤ (count - 1#64).toNat ∧
      (count - 1#64).toNat - snap.toNat + 1 = count.toNat - snap.toNat := by
  have enough : (1#64 : BitVec 64) ≤ count := by change 1 ≤ count.toNat; omega
  rw [BitVec.toNat_sub_of_le enough]
  change count.toNat - 1 = count.toNat - 1 ∧ snap.toNat ≤ count.toNat - 1 ∧
    count.toNat - 1 - snap.toNat + 1 = count.toNat - snap.toNat
  omega

theorem decrement_family {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (objects : ι → TableFamily.Object) (family : TableFamily.Model source cursor objects) (count : BitVec 64) :
    TableFamily.Model (Input.putGlobal source "journal_n" (count - 1#64)) cursor objects :=
  family.of_control (Input.putGlobal.lookup_other source "journal_n" _ (ofString "heap_ptr") (by decide)) rfl rfl rfl

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.condition_read
#print axioms InitECandidate.Solver.GasBudget.Journal.decrement_execute
#print axioms InitECandidate.Solver.GasBudget.Journal.decrement_progress
#print axioms InitECandidate.Solver.GasBudget.Journal.decrement_family
