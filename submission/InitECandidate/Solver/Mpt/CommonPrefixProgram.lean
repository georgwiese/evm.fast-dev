import InitECandidate.Solver.Input.GuardedCounterLoop
import InitECandidate.Solver.GasBudget.Minimum
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Mpt.KeyToNibblesAnyLoops

namespace InitECandidate.Solver.Mpt.CommonPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_common_prefix_length with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "a",.one),(ofString "al",.one),(ofString "b",.one),(ofString "bl",.one)]
def minimumArguments : List (ExpHOL 64):=[localVar "al",localVar "bl"]
def test : ExpHOL 64:=.cmp .lower (localVar "i") (localVar "n")
def mismatch : ExpHOL 64:=.cmp .notEqual (.loadByte (.op .add [localVar "a",localVar "i"])) (.loadByte (.op .add [localVar "b",localVar "i"]))
def guard : ProgHOL 64:=.ite mismatch (.return (localVar "i")) .skip
def advance : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def loopBody : ProgHOL 64:=.seq guard advance
def loopAndAfter : ProgHOL 64:=.seq (.while test loopBody) (.return (localVar "n"))
def afterMinimum : ProgHOL 64:=.dec (ofString "i") .one (.const 0#64) loopAndAfter

theorem body_shape : body=.decCall (ofString "n") .one (ofString "min") minimumArguments afterMinimum := by
  simp only [body,Guest.guestFn_common_prefix_length,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    minimumArguments,afterMinimum,loopAndAfter,test,loopBody,guard,mismatch,advance,localVar]

theorem guarded : Input.GuardedCounter 1 loopBody :=
  .checks (.ite _ (.returned _) .skip) .increment

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "common_prefix_length")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 225 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_common_prefix_length) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_common_prefix_length,Guest.guestFn_common_prefix_length,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
theorem minimum_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "min")=some (GasBudget.Minimum.formals,GasBudget.Minimum.body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 26 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_min) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,GasBudget.Minimum.formals,GasBudget.Minimum.body,Guest.Software.guestFn_min,Guest.guestFn_min,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem test_reads (length : Nat) (small : length≤64) : Input.GuardedCounterLoop.TestReads test 1 length :=
  KeyToNibbles.tail_reads length (by omega)

end InitECandidate.Solver.Mpt.CommonPrefix

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.body_shape
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.guarded
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.original_code
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.minimum_code
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.test_reads
