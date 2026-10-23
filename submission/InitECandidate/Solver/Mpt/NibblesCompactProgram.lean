import InitECandidate.Solver.Mpt.NibblesConcatProgram
import InitECandidate.Solver.Input.ByteStoreLocal
import InitECandidate.Solver.Input.ByteStoreClock

namespace InitECandidate.Solver.Mpt.NibblesCompact
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_nibble_list_to_compact with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "nibs",.one),(ofString "n",.one),(ofString "is_leaf",.one),(ofString "dst",.one)]
def afterFlag : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterCounter : ProgHOL 64:=match afterFlag with | .dec _ _ _ rest=>rest | _=>.skip
def header : ProgHOL 64:=match afterCounter with | .seq first _=>first | _=>.skip
def outputScope : ProgHOL 64:=match afterCounter with | .seq _ rest=>rest | _=>.skip
def afterOutput : ProgHOL 64:=match outputScope with | .dec _ _ _ rest=>rest | _=>.skip
def loop : ProgHOL 64:=match afterOutput with | .seq first _=>first | _=>.skip
def step : ProgHOL 64:=match loop with | .while _ rest=>rest | _=>.skip
def storePair : ProgHOL 64:=match step with | .seq first _=>first | _=>.skip
def pairAddress : ExpHOL 64:=.op .add [localVar "dst",localVar "o"]
def pairValue : ExpHOL 64:=.op .or
  [.shift .lsl (.loadByte (.op .add [localVar "nibs",localVar "i"])) (.const 4#64),
    .loadByte (.op .add [localVar "nibs",localVar "i",.const 1#64])]
def test : ExpHOL 64:=.cmp .lower (localVar "i") (localVar "n")
def flagExpression : ExpHOL 64:=.panop .mul [localVar "is_leaf",.const 2#64]
def evenTest : ExpHOL 64:=.cmp .equal (.op .and [localVar "n",.const 1#64]) (.const 0#64)
def evenHeader : ProgHOL 64:=.storeByte (localVar "dst") (.panop .mul [.const 16#64,localVar "flag"])
def oddStore : ProgHOL 64:=.storeByte (localVar "dst")
  (.op .add [.panop .mul [.const 16#64,.op .add [localVar "flag",.const 1#64]],.loadByte (localVar "nibs")])
def advance : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 2#64])
def advanceOutput : ProgHOL 64:=.assign .local (ofString "o") (.op .add [localVar "o",.const 1#64])

theorem body_shapes : body=.dec (ofString "flag") .one flagExpression afterFlag ∧
    afterFlag=.dec (ofString "i") .one (.const 0#64) afterCounter ∧
    afterCounter=.seq header outputScope ∧
    outputScope=.dec (ofString "o") .one (.const 1#64) afterOutput ∧
    afterOutput=.seq loop (.return (localVar "o")) ∧ loop=.while test step ∧
    step=.seq storePair (.seq advance advanceOutput) ∧
    header=.ite evenTest evenHeader (.seq oddStore (.assign .local (ofString "i") (.const 1#64))) := by
  simp only [body,afterFlag,afterCounter,header,outputScope,afterOutput,loop,step,storePair,test,flagExpression,
    evenTest,evenHeader,oddStore,advance,advanceOutput,Guest.guestFn_nibble_list_to_compact,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,localVar]
  simp

theorem store_pair_shape : storePair=.storeByte pairAddress pairValue := by
  simp only [storePair,step,loop,afterOutput,outputScope,afterCounter,afterFlag,body,pairAddress,pairValue,
    Guest.guestFn_nibble_list_to_compact,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "nibble_list_to_compact")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 226 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_nibble_list_to_compact) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_nibble_list_to_compact,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length leaf destination : BitVec 64)
    (known : source.code.lookup (ofString "nibble_list_to_compact")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite source.code.lookup (ofString "nibble_list_to_compact")
      [.val (.word pointer),.val (.word length),.val (.word leaf),.val (.word destination)]=some (body,callee,.one) ∧
      callee.lookup (ofString "nibs")=some (.val (.word pointer)) ∧ callee.lookup (ofString "n")=some (.val (.word length)) ∧
      callee.lookup (ofString "is_leaf")=some (.val (.word leaf)) ∧ callee.lookup (ofString "dst")=some (.val (.word destination)) :=
  Input.word_quad_environment source.code.lookup (ofString "nibble_list_to_compact") (ofString "nibs") (ofString "n")
    (ofString "is_leaf") (ofString "dst") body .one pointer length leaf destination
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) known

theorem step_summary (key : MlS) (notCounter : key≠ofString "i") (notOutput : key≠ofString "o") :
    ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,Input.LocalSummary key step source := by
  rw [body_shapes.2.2.2.2.2.2.1]
  rw [store_pair_shape]
  exact Input.local_summary_sequence key _ _ (Input.byte_store_local key _ _)
    (Input.LocalPrefix.seq (.assign _ _ notCounter) (.assign _ _ notOutput)).summary_full

theorem step_advance : Input.CounterFlow.Advances (ofString "i") 2 step := by
  rw [body_shapes.2.2.2.2.2.2.1]
  have stored : Input.CounterFlow.Advances (ofString "i") 0 storePair:=by
    rw [store_pair_shape]
    exact Input.CounterFlow.byte_store _ _ _
  simpa only [Nat.zero_add,Nat.add_zero,advance,advanceOutput,localVar] using Input.CounterFlow.sequence (ofString "i") _ _ 0 (2+0) stored
    (Input.CounterFlow.sequence (ofString "i") _ _ 2 0 (Input.CounterFlow.increment_by _ 2)
      (Input.CounterFlow.preserved _ _ (.assign _ _ (by decide))))

theorem step_cost (code) : Input.ClockCost.Bound code step 0 := by
  rw [body_shapes.2.2.2.2.2.2.1]
  rw [store_pair_shape]
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store_byte code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _))

theorem header_cost (code) : Input.ClockCost.Bound code header 0 := by
  rw [body_shapes.2.2.2.2.2.2.2]
  exact Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.store_byte code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store_byte code _ _) (Input.ClockCost.assign code _ _))

end InitECandidate.Solver.Mpt.NibblesCompact

#print axioms InitECandidate.Solver.Mpt.NibblesCompact.body_shapes
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.store_pair_shape
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.original_code
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.environment
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.step_summary
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.step_advance
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.step_cost
#print axioms InitECandidate.Solver.Mpt.NibblesCompact.header_cost
