import InitECandidate.Solver.GasBudget.JournalAppendProgram
import InitECandidate.Solver.MutableTable.DeleteRuntimeDefs

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def deleteSuffixPrice (kind : KeyHash.Kind) (population : Nat) : Nat := KeyHash.keySize kind + 2 + (Delete.modelPrice kind population + 1)
def deletePrice (kind : KeyHash.Kind) (population : Nat) : Nat := Get.bodyPrice kind population + 1 + deleteSuffixPrice kind population

theorem empty_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (flag value : BitVec 64)
    (old : source.locals.lookup (ofString "old") = some (Get.pair flag value)) :
    eval source emptyCondition = some (.val (.word (if flag = 0#64 then 1#64 else 0#64))) := by
  simp [eval, emptyCondition, localVar, evalHOLExact, toExact, old, Get.pair,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.empty_read
