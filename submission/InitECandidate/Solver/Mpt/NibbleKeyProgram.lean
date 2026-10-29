import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.LoadWordCase
import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Mpt.KeyToNibblesSmallNormal

namespace InitECandidate.Solver.Mpt.NibbleKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_mpt_nibble_key with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "m",.one),(ofString "key",.one),(ofString "klen",.one)]
def returnShape : ShapeHOL:=.comb [.one,.one]
def securedGuard : ProgHOL 64:=match body with | .seq first _=>first | _=>.skip
def securedBranch : ProgHOL 64:=match securedGuard with | .ite _ yes _=>yes | _=>.skip
def unsecured : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip
def securedAddress : ExpHOL 64:=.op .add [localVar "m",.const 8#64]
def securedTest : ExpHOL 64:=.cmp .notEqual (.load .one securedAddress) (.const 0#64)
def amount : ExpHOL 64:=.panop .mul [.const 2#64,localVar "klen"]
def convertArguments : List (ExpHOL 64):=[localVar "key",localVar "klen",localVar "nb2"]
def convert : ProgHOL 64:=.call (some (none,none)) (ofString "key_to_nibbles") convertArguments
def result : ExpHOL 64:=.rstruct [localVar "nb2",amount]
def tail : ProgHOL 64:=.seq convert (.return result)
def actions : List Input.CallPrefix.Action:=[.scoped (ofString "nb2") .one (ofString "alloc") [amount]]

theorem body_shape : body=.seq (.ite securedTest securedBranch .skip) unsecured := by
  simp only [body,securedTest,securedBranch,securedGuard,unsecured,securedAddress,localVar,
    Guest.guestFn_mpt_nibble_key,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem unsecured_shape : unsecured=.decCall (ofString "nb2") .one (ofString "alloc") [amount] tail := by
  simp only [unsecured,body,Guest.guestFn_mpt_nibble_key,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,amount,tail,convert,convertArguments,result,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mpt_nibble_key")=some (formals,body,returnShape) := by
  have checked:=Input.OriginalCode.indexed code installed 244 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_mpt_nibble_key) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,returnShape,
    Guest.Software.guestFn_mpt_nibble_key,Guest.guestFn_mpt_nibble_key,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (m key length : BitVec 64)
    (known : table (ofString "mpt_nibble_key")=some (formals,body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "mpt_nibble_key") [.val (.word m),.val (.word key),.val (.word length)]=some (body,callee,returnShape) ∧
      callee.lookup (ofString "m")=some (.val (.word m)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) ∧
      callee.lookup (ofString "klen")=some (.val (.word length)) :=
  Input.word_triple_environment table (ofString "mpt_nibble_key") (ofString "m") (ofString "key") (ofString "klen") body returnShape m key length
    (by decide) (by decide) (by decide) known

theorem unsecured_run (source : PanSemStateFiniteExact 64 Guest.HostMemory) (m : BitVec 64)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64) :
    evaluateHOLFiniteState source body=evaluateHOLFiniteState source unsecured := by
  have addressRead : eval source securedAddress=some (.val (.word (m+8#64))):=by
    simp [eval,securedAddress,localVar,evalHOLExact,evalListHOLExact,toExact,mCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have loadRead : eval source (.load .one securedAddress)=some (.val (.word 0#64)):=by
    rw [Input.load_one_case source securedAddress (m+8#64) 0#64 addressRead cell,if_pos mapped]
  have testRead : eval source securedTest=some (.val (.word 0#64)):=by
    simp only [eval] at loadRead ⊢
    rw [securedTest,evalHOLExact,loadRead]
    rfl
  have guardRun : evaluateHOLFiniteState source (.ite securedTest securedBranch .skip)=(none,source):=by
    rw [evaluateHOLFiniteState_ite]
    simp only [eval] at testRead
    rw [testRead]
    simp [evaluateHOLFiniteState_skip]
  rw [body_shape,StateSteps.next_sequence source source _ _ guardRun (Nat.le_refl _)]

theorem allocation_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (m : BitVec 64)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (mapped : source.memaddrs (m+8#64)) (cell : source.memory (m+8#64)=.word 0#64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ current inner,Input.CallPrefix.Execution source actions current ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current tail=(some (.returned value),inner) := by
  rw [unsecured_run source m mCell mapped cell,unsecured_shape] at normal
  exact Input.CallPrefix.normal_trace source post actions tail value (Input.NoReturn.scoped_call _ _ _ _ _ Input.NoReturn.skip) normal

end InitECandidate.Solver.Mpt.NibbleKey

#print axioms InitECandidate.Solver.Mpt.NibbleKey.body_shape
#print axioms InitECandidate.Solver.Mpt.NibbleKey.unsecured_shape
#print axioms InitECandidate.Solver.Mpt.NibbleKey.original_code
#print axioms InitECandidate.Solver.Mpt.NibbleKey.environment
#print axioms InitECandidate.Solver.Mpt.NibbleKey.unsecured_run
#print axioms InitECandidate.Solver.Mpt.NibbleKey.allocation_trace
