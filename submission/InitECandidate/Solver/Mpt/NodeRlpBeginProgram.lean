import InitECandidate.Solver.Mpt.NibblesCompactCall
import InitECandidate.Solver.Mpt.ValueEncodedLenCall
import InitECandidate.Solver.Input.WordStoreNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__node_rlp_begin with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "fr",.one),(ofString "node",.one)]
def nodeField (offset : Nat) : ExpHOL 64:=.load .one (.op .add [localVar "node",.const (BitVec.ofNat 64 offset)])
def frameAddress (offset : Nat) : ExpHOL 64:=.op .add [localVar "fr",.const (BitVec.ofNat 64 offset)]
def afterTag : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterPayload : ProgHOL 64:=match afterTag with | .dec _ _ _ rest=>rest | _=>.skip
def afterBuffer : ProgHOL 64:=match afterPayload with | .dec _ _ _ rest=>rest | _=>.skip
def afterLength : ProgHOL 64:=match afterBuffer with | .dec _ _ _ rest=>rest | _=>.skip
def pathChoice : ProgHOL 64:=match afterLength with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match afterLength with | .seq _ rest=>rest | _=>.skip
def pathScope : ProgHOL 64:=match pathChoice with | .ite _ yes _=>yes | _=>.skip
def afterPathLength : ProgHOL 64:=match pathScope with | .dec _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match afterPathLength with | .seq _ rest=>rest | _=>.skip
def afterLeafFlag : ProgHOL 64:=match afterAllocation with | .dec _ _ _ rest=>rest | _=>.skip
def compactAndLengths : ProgHOL 64:=match afterLeafFlag with | .seq _ rest=>rest | _=>.skip
def lengthScope : ProgHOL 64:=match compactAndLengths with | .seq _ rest=>rest | _=>.skip
def afterEncoded : ProgHOL 64:=match lengthScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def compactArguments : List (ExpHOL 64):=[nodeField 32,localVar "nlen",localVar "isl",localVar "cbuf"]
def allocationArguments : List (ExpHOL 64):=[.op .add [.shift .lsr (localVar "nlen") (.const 1#64),.const 2#64]]
def compactCall : ProgHOL 64:=.call (some (some (.local,ofString "clen"),none)) (ofString "nibble_list_to_compact") compactArguments
def leafChoice : ProgHOL 64:=match afterEncoded with | .seq _ rest=>rest | _=>.skip
def assignPath : ProgHOL 64:=.assign .local (ofString "payload") (localVar "el")
def leafArguments : List (ExpHOL 64):=[nodeField 48,nodeField 56]
def addLeaf : ProgHOL 64:=.assign .local (ofString "payload") (.op .add [localVar "payload",localVar "vl"])
def leafValueCall : ProgHOL 64:=.decCall (ofString "vl") .one (ofString "rlp_value_encoded_len") leafArguments addLeaf

theorem body_shapes : body=.dec (ofString "k") .one (nodeField 0) afterTag ∧
    afterTag=.dec (ofString "payload") .one (.const 0#64) afterPayload ∧
    afterPayload=.dec (ofString "cbuf") .one (.const 0#64) afterBuffer ∧
    afterBuffer=.dec (ofString "clen") .one (.const 0#64) afterLength ∧
    afterLength=.seq pathChoice footer ∧
    pathChoice=.ite (.cmp .notEqual (localVar "k") (.const 3#64)) pathScope .skip := by
  simp only [body,afterTag,afterPayload,afterBuffer,afterLength,pathChoice,footer,pathScope,nodeField,
    Guest.guestFn__node_rlp_begin,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]
  simp

theorem footer_shape : footer=.seq (.store (frameAddress 24) (localVar "cbuf"))
    (.seq (.store (frameAddress 32) (localVar "clen"))
      (.seq (.store (frameAddress 40) (localVar "payload")) (.return (.const 0#64)))) := by
  simp only [footer,afterLength,afterBuffer,afterPayload,afterTag,body,frameAddress,Guest.guestFn__node_rlp_begin,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

theorem path_shapes : pathScope=.dec (ofString "nlen") .one (nodeField 40) afterPathLength ∧
    afterPathLength=.seq (.call (some (some (.local,ofString "cbuf"),none)) (ofString "alloc") allocationArguments) afterAllocation ∧
    afterAllocation=.dec (ofString "isl") .one (.const 0#64) afterLeafFlag ∧
    afterLeafFlag=.seq (.ite (.cmp .equal (localVar "k") (.const 1#64)) (.assign .local (ofString "isl") (.const 1#64)) .skip) compactAndLengths ∧
    compactAndLengths=.seq compactCall lengthScope ∧
    lengthScope=.decCall (ofString "el") .one (ofString "rlp_bytes_encoded_len") [.loadByte (localVar "cbuf"),localVar "clen"] afterEncoded := by
  simp only [pathScope,pathChoice,afterLength,afterBuffer,afterPayload,afterTag,body,afterPathLength,afterAllocation,afterLeafFlag,
    compactAndLengths,lengthScope,afterEncoded,compactCall,compactArguments,allocationArguments,nodeField,
    Guest.guestFn__node_rlp_begin,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]
  simp

theorem after_encoded_shapes : afterEncoded=.seq assignPath leafChoice ∧
    leafChoice=.ite (.cmp .equal (localVar "k") (.const 1#64)) leafValueCall .skip := by
  simp only [afterEncoded,lengthScope,compactAndLengths,afterLeafFlag,afterAllocation,afterPathLength,pathScope,pathChoice,
    afterLength,afterBuffer,afterPayload,afterTag,body,leafChoice,assignPath,leafValueCall,leafArguments,addLeaf,nodeField,
    Guest.guestFn__node_rlp_begin,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,localVar]
  simp

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_node_rlp_begin")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 257 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__node_rlp_begin) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__node_rlp_begin,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (frame node : BitVec 64)
    (known : codeFn (ofString "_node_rlp_begin")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "_node_rlp_begin") [.val (.word frame),.val (.word node)]=some (body,callee,.one) ∧
      callee.lookup (ofString "fr")=some (.val (.word frame)) ∧ callee.lookup (ofString "node")=some (.val (.word node)) :=
  Input.word_pair_environment codeFn (ofString "_node_rlp_begin") (ofString "fr") (ofString "node") body .one frame node (by decide) known

theorem footer_cost (code) : Input.ClockCost.Bound code footer 0 := by
  rw [footer_shape]
  exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
      (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.returned code _)))

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.body_shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.footer_shape
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.path_shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_encoded_shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.original_code
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.environment
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.footer_cost
