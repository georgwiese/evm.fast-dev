import InitECandidate.Solver.Mpt.NewCall
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_build_mpt_indexed with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "slice_arr",.one),(ofString "n",.one),(ofString "out",.one)]
def values (array count out : BitVec 64) : List (ValueHOL 64):=[.val (.word array),.val (.word count),.val (.word out)]
def afterMark : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterNew : ProgHOL 64:=match afterMark with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loopAndAfter : ProgHOL 64:=match afterNew with | .dec _ _ _ rest=>rest | _=>.skip
def loop : ProgHOL 64:=match loopAndAfter with | .seq first _=>first | _=>.skip
def afterLoop : ProgHOL 64:=match loopAndAfter with | .seq _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .lower (localVar "i") (localVar "n")
def loopBody : ProgHOL 64:=match loop with | .while _ body=>body | _=>.skip
def actions : List Input.CallPrefix.Action:=[
  .scoped (ofString "mark") .one (ofString "heap_mark") [],
  .scoped (ofString "m") .one (ofString "mpt_new") [.const 0#64,.const 0#64],
  .declare (ofString "i") .one (.const 0#64)]

theorem body_shape : body=Input.CallPrefix.program actions loopAndAfter := by
  simp only [body,Guest.guestFn_build_mpt_indexed,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    actions,Input.CallPrefix.program,loopAndAfter,afterNew,afterMark] <;>rfl

theorem loop_shape : loopAndAfter=.seq (.while test loopBody) afterLoop := by
  simp only [loopAndAfter,afterNew,afterMark,body,Guest.guestFn_build_mpt_indexed,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,loop,loopBody,afterLoop,test,localVar] <;>rfl

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "build_mpt_indexed")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 268 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_build_mpt_indexed) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_build_mpt_indexed,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (array count out : BitVec 64)
    (code : codeFn (ofString "build_mpt_indexed")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "build_mpt_indexed") (values array count out)=some (body,callee,.one) ∧
      callee.lookup (ofString "slice_arr")=some (.val (.word array)) ∧ callee.lookup (ofString "n")=some (.val (.word count)) ∧
      callee.lookup (ofString "out")=some (.val (.word out)) :=
  Input.word_triple_environment codeFn (ofString "build_mpt_indexed") (ofString "slice_arr") (ofString "n") (ofString "out") body .one
    array count out (by decide) (by decide) (by decide) code

theorem prefix_never : Input.NoReturn.Never (Input.CallPrefix.program actions .skip) :=
  Input.NoReturn.scoped_call _ _ _ _ _ (Input.NoReturn.scoped_call _ _ _ _ _ (Input.NoReturn.declared _ _ _ _ Input.NoReturn.skip))

theorem setup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ current inner,Input.CallPrefix.Execution source actions current ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current loopAndAfter=(some (.returned value),inner) := by
  rw [body_shape] at normal
  exact Input.CallPrefix.normal_trace source post actions loopAndAfter value prefix_never normal

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.body_shape
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_shape
#print axioms InitECandidate.Solver.Mpt.Indexed.original_code
#print axioms InitECandidate.Solver.Mpt.Indexed.environment
#print axioms InitECandidate.Solver.Mpt.Indexed.prefix_never
#print axioms InitECandidate.Solver.Mpt.Indexed.setup_trace
