import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordQuadEnvironment
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn_nibbles_concat with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "a",.one),(ofString "al",.one),(ofString "b",.one),(ofString "bl",.one)]
def afterAllocation : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterFirst : ProgHOL 64:=match afterAllocation with | .seq _ rest=>rest | _=>.skip
def footer : ProgHOL 64:=match afterFirst with | .seq _ rest=>rest | _=>.skip
def amountExpression : ExpHOL 64:=.op .add [localVar "al",localVar "bl"]
def allocationArguments : List (ExpHOL 64):=[amountExpression]
def firstArguments : List (ExpHOL 64):=[localVar "out",localVar "a",localVar "al"]
def secondArguments : List (ExpHOL 64):=[.op .add [localVar "out",localVar "al"],localVar "b",localVar "bl"]
def firstCopy : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") firstArguments
def secondCopy : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") secondArguments

theorem body_shapes : body=.decCall (ofString "out") .one (ofString "alloc") allocationArguments afterAllocation ∧
    afterAllocation=.seq firstCopy afterFirst ∧ afterFirst=.seq secondCopy footer ∧ footer=.return (localVar "out") := by
  simp only [body,afterAllocation,afterFirst,footer,allocationArguments,amountExpression,firstCopy,firstArguments,secondCopy,secondArguments,
    Guest.Software.guestFn_nibbles_concat,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "nibbles_concat")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 226 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_nibbles_concat) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn_nibbles_concat,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def callValues (a al b bl : BitVec 64) : List (ValueHOL 64):=[.val (.word a),.val (.word al),.val (.word b),.val (.word bl)]

theorem environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a al b bl : BitVec 64)
    (known : source.code.lookup (ofString "nibbles_concat")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite source.code.lookup (ofString "nibbles_concat") (callValues a al b bl)=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "al")=some (.val (.word al)) ∧
      callee.lookup (ofString "b")=some (.val (.word b)) ∧ callee.lookup (ofString "bl")=some (.val (.word bl)) :=
  Input.word_quad_environment source.code.lookup (ofString "nibbles_concat") (ofString "a") (ofString "al") (ofString "b") (ofString "bl") body .one a al b bl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) known

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.body_shapes
#print axioms InitECandidate.Solver.Mpt.NibblesConcat.original_code
#print axioms InitECandidate.Solver.Mpt.NibblesConcat.environment
