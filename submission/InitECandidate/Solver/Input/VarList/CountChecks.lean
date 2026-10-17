import InitECandidate.Solver.Input.VarList.FirstChecks

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocationCall : ProgHOL 64 := .decCall (ofString "arr") .one (ofString "alloc") [allocationExpression] allocatedTail

theorem count_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count limit : BitVec 64)
    (c : source.locals.lookup (ofString "count")=some (.val (.word count)))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit))) :
    eval source countTest=some (.val (.word (if limit<count then 1#64 else 0#64))) := by
  classical
  simp [eval,countTest,localVar,evalHOLExact,toExact,c,l,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem allocation_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64)
    (c : source.locals.lookup (ofString "count")=some (.val (.word count))) :
    eval source allocationExpression=some (.val (.word (count*16#64))) := by
  classical
  simp [eval,allocationExpression,localVar,evalHOLExact,evalListHOLExact,toExact,c,valueIsWord,valueWord,panOpHOL]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.count_test_read
#print axioms InitECandidate.Solver.Input.VarList.allocation_read
