import InitECandidate.Solver.Mpt.DestroyStorageLoop
import InitECandidate.Solver.GasBudget.JournalAppendDeleteRegistered

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable GasBudget

set_option maxRecDepth 100000 in
theorem journal_delete_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "jdel") = some (Find.formals,Journal.Append.deleteBody,.one) := by
  have checked := Input.OriginalCode.indexed code installed 325 (OriginalCodeEnvironment.originalEntry Guest.guestFn_jdel) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Find.formals,Journal.Append.deleteBody,
    Guest.guestFn_jdel,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem table_delete_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_del") = some (Find.formals,Delete.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 125 (OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_del) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Find.formals,Delete.body,
    Guest.guestFn_htab_del,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.journal_delete_code
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.table_delete_code
