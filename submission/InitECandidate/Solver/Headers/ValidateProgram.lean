import InitECandidate.Solver.Headers.DecodeCallTrace

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_validate_headers with | .function fn=>progToHOL fn.body | _=>.skip
def afterGuard : ProgHOL 64 := match body with | .seq _ rest=>rest | _=>.skip
def afterHs : ProgHOL 64 := match afterGuard with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterHashes : ProgHOL 64 := match afterHs with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loops : ProgHOL 64 := match afterHashes with | .dec _ _ _ rest=>rest | _=>.skip
def decodeStep : ProgHOL 64 := match loops with | .seq (.while _ step) _=>step | _=>.skip
def afterDecode : ProgHOL 64 := match loops with | .seq _ rest=>rest | _=>.skip
def linkTail : ProgHOL 64 := match afterDecode with | .seq _ rest=>rest | _=>.skip
def linkStep : ProgHOL 64 := match linkTail with | .seq (.while _ step) _=>step | _=>.skip
def afterHeader : ProgHOL 64 := match decodeStep with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterLink : ProgHOL 64 := match linkStep with | .decCall _ _ _ _ rest=>rest | _=>.skip

def formals : List (MlS×ShapeHOL) := [(ofString "arr",.one),(ofString "n",.one)]
def resultShape : ShapeHOL := .comb [.one,.one]
def countGuard : ProgHOL 64 := .ite (.cmp .lower (.const 256#64) (localVar "n")) (.raise (ofString "BlockErr") (.const 1#64)) .skip
def hsAmount : ExpHOL 64 := .op .add [.panop .mul [localVar "n",.const 8#64],.const 8#64]
def hashesAmount : ExpHOL 64 := .op .add [.panop .mul [localVar "n",.const 32#64],.const 32#64]
def test : ExpHOL 64 := .cmp .less (localVar "i") (localVar "n")
def row : ExpHOL 64 := .op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64]]
def rowLength : ExpHOL 64 := .op .add [localVar "arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]
def decodeArguments : List (ExpHOL 64) := [.load .one row,.load .one rowLength]
def headerCell : ExpHOL 64 := .op .add [localVar "hs",.panop .mul [localVar "i",.const 8#64]]
def hashCell : ExpHOL 64 := .op .add [localVar "hashes",.panop .mul [localVar "i",.const 32#64]]
def hashArguments : List (ExpHOL 64) := [.load .one row,.load .one rowLength,hashCell]
def linkArguments : List (ExpHOL 64) := [.load .one (.op .add [.load .one headerCell,.const 8#64]),
  .op .add [localVar "hashes",.panop .mul [.op .sub [localVar "i",.const 1#64],.const 32#64]],.const 32#64]
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def linkGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "eq") (.const 0#64)) (.raise (ofString "BlockErr") (.const 2#64)) .skip

set_option maxRecDepth 100000 in
/-- Exact unchanged validation program, including its signed loop tests,
actual raw-header hash arguments and previous-header hash comparison. -/
theorem shapes : body=.seq countGuard afterGuard ∧
    afterGuard=.decCall (ofString "hs") .one (ofString "alloc") [hsAmount] afterHs ∧
    afterHs=.decCall (ofString "hashes") .one (ofString "alloc") [hashesAmount] afterHashes ∧
    afterHashes=.dec (ofString "i") .one (.const 0#64) loops ∧
    loops=.seq (.while test decodeStep) afterDecode ∧
    afterDecode=.seq (.assign .local (ofString "i") (.const 1#64)) linkTail ∧
    linkTail=.seq (.while test linkStep) (.return (.rstruct [localVar "hs",localVar "hashes"])) ∧
    decodeStep=.decCall (ofString "h") .one (ofString "decode_header") decodeArguments afterHeader ∧
    afterHeader=.seq (.store headerCell (localVar "h")) (.seq (.call (some (none,none)) (ofString "keccak256") hashArguments) increment) ∧
    linkStep=.decCall (ofString "eq") .one (ofString "memeq") linkArguments afterLink ∧
    afterLink=.seq linkGuard increment := by
  simp only [body,afterGuard,afterHs,afterHashes,loops,decodeStep,afterDecode,linkTail,linkStep,afterHeader,afterLink,
    countGuard,hsAmount,hashesAmount,test,row,rowLength,decodeArguments,headerCell,hashCell,hashArguments,linkArguments,increment,linkGuard,
    localVar,Guest.guestFn_validate_headers,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "validate_headers")=some (formals,body,resultShape) := by
  have checked:=Input.OriginalCode.indexed code installed 214 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_validate_headers) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,resultShape,
    Guest.guestFn_validate_headers,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.shapes
#print axioms InitECandidate.Solver.Headers.Validate.original_code
