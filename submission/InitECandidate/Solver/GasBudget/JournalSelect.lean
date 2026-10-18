import InitECandidate.Solver.GasBudget.JournalRecords
import InitECandidate.Solver.GasBudget.JournalSet
import InitECandidate.Solver.GasBudget.JournalDelete
import InitECandidate.Solver.MutableTable.FamilyPotential

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

structure CallLocals {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → TableFamily.Object) (base index : Nat) (entry : Entry ι) : Prop where
  record : source.locals.lookup (ofString "r") = some (.val (.word (entryAddress base index 0)))
  table : source.locals.lookup (ofString "t") = some (.val (.word (objects entry.writer).pointer))
  key : source.locals.lookup (ofString "key") = some (.val (.word entry.key))

theorem CallLocals.entered {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → TableFamily.Object) (base index : Nat) (entry : Entry ι) :
    CallLocals (entered source objects base index entry) objects base index entry := by
  constructor
  · exact (bind_lookup_other _ "key" "r" _ (by decide)).trans ((bind_lookup_other _ "t" "r" _ (by decide)).trans (bind_lookup_same _ _ _))
  · exact (bind_lookup_other _ "key" "t" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _

def stepPrice (kind : KeyHash.Kind) (count : Nat) : Nat := max (Set.noGrowthPrice kind count + 1) (Delete.modelPrice kind count + 1)

theorem step_price_bound (kind : KeyHash.Kind) (count : Nat) : stepPrice kind count ≤ 38 * count + 39 := by
  rw [stepPrice, max_le_iff, Set.no_growth_caller_price, Delete.model_caller_price]
  cases kind <;> dsimp only <;> omega

theorem select_read {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base count index : Nat) (entries : Nat → Entry ι) (inside : index < count)
    (image : Image source objects base count entries) (locals : CallLocals source objects base index (entries index)) :
    evaluateHOLFiniteState source selectCall =
      evaluateHOLFiniteState source (if (entries index).flag = 0#64 then deleteCall else setCall) := by
  have read := field_read source base index 2 (entries index).flag locals.record (image.mapped index inside 2) (image.words index inside 2)
  change eval source (recordField 16#64) = some (.val (.word (entries index).flag)) at read
  simp only [eval] at read
  rw [selectCall, evaluateHOLFiniteState_ite, evalHOLExact, read]
  by_cases zero : (entries index).flag = 0#64 <;>
    simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero]

theorem set_arguments {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base count index : Nat) (entries : Nat → Entry ι) (inside : index < count)
    (image : Image source objects base count entries) (locals : CallLocals source objects base index (entries index)) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "t", localVar "key", recordField 24#64] =
      some (TableCall.values (objects (entries index).writer).pointer (entries index).key (entries index).value) := by
  have read := field_read source base index 3 (entries index).value locals.record (image.mapped index inside 3) (image.words index inside 3)
  change eval source (recordField 24#64) = some (.val (.word (entries index).value)) at read
  simp only [eval] at read
  simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, locals.table, locals.key, read, TableCall.values]

theorem delete_arguments {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base index : Nat) (entry : Entry ι) (locals : CallLocals source objects base index entry) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t", localVar "key"] =
      some [.val (.word (objects entry.writer).pointer), .val (.word entry.key)] := by
  simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, locals.table, locals.key]

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.CallLocals.entered
#print axioms InitECandidate.Solver.GasBudget.Journal.step_price_bound
#print axioms InitECandidate.Solver.GasBudget.Journal.select_read
#print axioms InitECandidate.Solver.GasBudget.Journal.set_arguments
#print axioms InitECandidate.Solver.GasBudget.Journal.delete_arguments
