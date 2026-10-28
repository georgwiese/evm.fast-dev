import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := Code.body .htr_pcontainer
def formals : List (MlS×ShapeHOL) := [(ofString "ch",.one),(ofString "n",.one),(ofString "out",.one)]
def afterMark : ProgHOL 64 := match body with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterTmp : ProgHOL 64 := match afterMark with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterProgressive : ProgHOL 64 := match afterTmp with | .seq _ tail=>tail | _=>.skip
def afterAct : ProgHOL 64 := match afterProgressive with | .dec _ _ _ tail=>tail | _=>.skip
def afterZero : ProgHOL 64 := match afterAct with | .seq _ tail=>tail | _=>.skip
def loopAndSuffix : ProgHOL 64 := match afterZero with | .dec _ _ _ tail=>tail | _=>.skip
def bitLoop : ProgHOL 64 := match loopAndSuffix with | .seq front _=>front | _=>.skip
def afterLoop : ProgHOL 64 := match loopAndSuffix with | .seq _ tail=>tail | _=>.skip
def afterSha : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))
def test : ExpHOL 64 := .cmp .less (localVar "i") (localVar "n")
def bitStep : ProgHOL 64 := match bitLoop with | .while _ step=>step | _=>.skip
def bitAddress : ExpHOL 64 := .op .add [localVar "act",.shift .lsr (localVar "i") (.const 3#64)]
def bitValue : ExpHOL 64 := .op .or [.loadByte bitAddress,.shift .lsl (.const 1#64) (.op .and [localVar "i",.const 7#64])]
def progressiveArguments : List (ExpHOL 64) := [localVar "ch",localVar "n",localVar "tmp"]
def zeroArguments : List (ExpHOL 64) := [localVar "act",.const 32#64]
def shaArguments : List (ExpHOL 64) := [localVar "tmp",localVar "act",localVar "out"]

set_option maxRecDepth 100000 in
theorem body_shape :
    body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark ∧
    afterMark=.decCall (ofString "tmp") .one (ofString "alloc") [.const 64#64] afterTmp ∧
    afterTmp=.seq (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) afterProgressive ∧
    afterProgressive=.dec (ofString "act") .one (.op .add [localVar "tmp",.const 32#64]) afterAct ∧
    afterAct=.seq (.call (some (none,none)) (ofString "memzero") zeroArguments) afterZero ∧
    afterZero=.dec (ofString "i") .one (.const 0#64) loopAndSuffix ∧
    loopAndSuffix=.seq bitLoop afterLoop ∧ bitLoop=.while test bitStep ∧
    bitStep=.seq (.storeByte bitAddress bitValue) (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])) ∧
    afterLoop=.seq (.call (some (none,none)) (ofString "sha256_pair") shaArguments) afterSha := by
  simp only [body,afterMark,afterTmp,afterProgressive,afterAct,afterZero,loopAndSuffix,bitLoop,bitStep,afterLoop,afterSha,
    Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_pcontainer,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    progressiveArguments,zeroArguments,shaArguments,test,bitAddress,bitValue,localVar]
  exact ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_pcontainer")=some (formals,body,.one) := by
  simpa only [Code.name, Code.formals, Code.body, Code.shape, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, formals, body,
    Guest.Software.guestFn_htr_pcontainer, shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
    using Code.installed code installed .htr_pcontainer

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.body_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.original_code
