import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.WordEnvironment

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn__mpt_delete_node_body with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one),(ofString "key",.one),(ofString "klen",.one),(ofString "level",.one)]
def afterTop : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterResult : ProgHOL 64:=match afterTop with | .dec _ _ _ rest=>rest | _=>.skip
def afterGo : ProgHOL 64:=match afterResult with | .dec _ _ _ rest=>rest | _=>.skip
def descent : ProgHOL 64:=match afterGo with | .seq first _=>first | _=>.skip
def afterDescent : ProgHOL 64:=match afterGo with | .seq _ rest=>rest | _=>.skip
def unwind : ProgHOL 64:=match afterDescent with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match afterDescent with | .seq _ rest=>rest | _=>.skip
def descentBody : ProgHOL 64:=match descent with | .while _ inner=>inner | _=>.skip
def nodeChoice : ProgHOL 64:=match descentBody with | .seq _ rest=>rest | _=>.skip
def nonempty : ProgHOL 64:=match nodeChoice with | .ite _ _ rest=>rest | _=>.skip
def afterKind : ProgHOL 64:=match nonempty with | .dec _ _ _ rest=>rest | _=>.skip
def hashGuard : ProgHOL 64:=match afterKind with | .seq first _=>first | _=>.skip
def afterHash : ProgHOL 64:=match afterKind with | .seq _ rest=>rest | _=>.skip
def kindChoice : ProgHOL 64:=match afterHash with | .seq _ rest=>rest | _=>.skip
def leafBlock : ProgHOL 64:=match kindChoice with | .ite _ first _=>first | _=>.skip
def nonleaf : ProgHOL 64:=match kindChoice with | .ite _ _ rest=>rest | _=>.skip
def extensionBlock : ProgHOL 64:=match nonleaf with | .ite _ first _=>first | _=>.skip
def branchBlock : ProgHOL 64:=match nonleaf with | .ite _ _ rest=>rest | _=>.skip
def afterSegment : ProgHOL 64:=match extensionBlock with | .dec _ _ _ rest=>rest | _=>.skip
def prefixScope : ProgHOL 64:=match afterSegment with | .dec _ _ _ rest=>rest | _=>.skip
def prefixChoice : ProgHOL 64:=match prefixScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def extensionFrameScope : ProgHOL 64:=match prefixChoice with | .ite _ _ rest=>rest | _=>.skip
def extensionPush : ProgHOL 64:=match extensionFrameScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def branchValue : ProgHOL 64:=match branchBlock with | .ite _ first _=>first | _=>.skip
def branchIndexScope : ProgHOL 64:=match branchBlock with | .ite _ _ rest=>rest | _=>.skip
def branchFrameScope : ProgHOL 64:=match branchIndexScope with | .dec _ _ _ rest=>rest | _=>.skip
def branchPush : ProgHOL 64:=match branchFrameScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def unwindBody : ProgHOL 64:=match unwind with | .while _ inner=>inner | _=>.skip
def afterFrameNode : ProgHOL 64:=match unwindBody with | .dec _ _ _ rest=>rest | _=>.skip
def unwindChoice : ProgHOL 64:=match afterFrameNode with | .seq first _=>first | _=>.skip
def pop : ProgHOL 64:=match afterFrameNode with | .seq _ rest=>rest | _=>.skip

def field (name : String) (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar name,.const offset])
def childAddress (name : String) (index : ExpHOL 64) : ExpHOL 64:=
  .op .add [localVar name,.const 32#64,.panop .mul [index,.const 8#64]]
def remaining : ExpHOL 64:=.op .sub [localVar "klen",localVar "level"]
def keySuffix : ExpHOL 64:=.op .add [localVar "key",localVar "level"]
def descentTest : ExpHOL 64:=.cmp .notEqual (localVar "go") (.const 0#64)
def unwindTest : ExpHOL 64:=.cmp .notEqual (localVar "top") (.const 0#64)

theorem setup_shapes : body=.dec (ofString "top") .one (.const 0#64) afterTop ∧
    afterTop=.dec (ofString "res") .one (.const 0#64) afterResult ∧
    afterResult=.dec (ofString "go") .one (.const 1#64) afterGo ∧
    afterGo=.seq descent afterDescent ∧ afterDescent=.seq unwind footer ∧ footer=.return (localVar "res") := by
  simp only [body, afterTop, afterResult, afterGo, descent, afterDescent, unwind, footer, descentBody, nodeChoice, nonempty, afterKind, hashGuard, afterHash, kindChoice, leafBlock, nonleaf, extensionBlock, branchBlock, afterSegment, prefixScope, prefixChoice, extensionFrameScope, extensionPush, branchValue, branchIndexScope, branchFrameScope, branchPush, unwindBody, afterFrameNode, unwindChoice, pop, field, childAddress, remaining, keySuffix, descentTest, unwindTest, Guest.guestFn__mpt_delete_node_body, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> simp

theorem descent_shapes : descent=.while descentTest descentBody ∧
    descentBody=.seq (.assign .local (ofString "go") (.const 0#64)) nodeChoice ∧
    nodeChoice=.ite (.cmp .equal (localVar "node") (.const 0#64)) (.assign .local (ofString "res") (.const 0#64)) nonempty ∧
    nonempty=.dec (ofString "k") .one (field "node" 0#64) afterKind ∧
    afterKind=.seq hashGuard afterHash ∧
    hashGuard=.ite (.cmp .equal (localVar "k") (.const 0#64)) (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]) .skip ∧
    afterHash=.seq (.call (some (none,none)) (ofString "node_invalidate") [localVar "node"]) kindChoice ∧
    kindChoice=.ite (.cmp .equal (localVar "k") (.const 1#64)) leafBlock nonleaf ∧
    nonleaf=.ite (.cmp .equal (localVar "k") (.const 2#64)) extensionBlock branchBlock := by
  simp only [body, afterTop, afterResult, afterGo, descent, afterDescent, unwind, footer, descentBody, nodeChoice, nonempty, afterKind, hashGuard, afterHash, kindChoice, leafBlock, nonleaf, extensionBlock, branchBlock, afterSegment, prefixScope, prefixChoice, extensionFrameScope, extensionPush, branchValue, branchIndexScope, branchFrameScope, branchPush, unwindBody, afterFrameNode, unwindChoice, pop, field, childAddress, remaining, keySuffix, descentTest, unwindTest, Guest.guestFn__mpt_delete_node_body, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> simp

theorem leaf_shape : leafBlock=.seq (.assign .local (ofString "res") (localVar "node"))
    (.ite (.cmp .equal (field "node" 40#64) remaining)
      (.decCall (ofString "eq") .one (ofString "memeq") [field "node" 32#64,keySuffix,remaining]
        (.ite (.cmp .notEqual (localVar "eq") (.const 0#64)) (.assign .local (ofString "res") (.const 0#64)) .skip)) .skip) := by
  simp only [body, afterTop, afterResult, afterGo, descent, afterDescent, unwind, footer, descentBody, nodeChoice, nonempty, afterKind, hashGuard, afterHash, kindChoice, leafBlock, nonleaf, extensionBlock, branchBlock, afterSegment, prefixScope, prefixChoice, extensionFrameScope, extensionPush, branchValue, branchIndexScope, branchFrameScope, branchPush, unwindBody, afterFrameNode, unwindChoice, pop, field, childAddress, remaining, keySuffix, descentTest, unwindTest, Guest.guestFn__mpt_delete_node_body, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> simp

theorem extension_shapes : extensionBlock=.dec (ofString "seg") .one (field "node" 32#64) afterSegment ∧
    afterSegment=.dec (ofString "sl") .one (field "node" 40#64) prefixScope ∧
    prefixScope=.decCall (ofString "pl") .one (ofString "common_prefix_length") [localVar "seg",localVar "sl",keySuffix,remaining] prefixChoice ∧
    prefixChoice=.ite (.cmp .lower (localVar "pl") (localVar "sl")) (.assign .local (ofString "res") (localVar "node")) extensionFrameScope ∧
    extensionFrameScope=.decCall (ofString "fr") .one (ofString "scratch_alloc") [.const 40#64] extensionPush := by
  simp only [body, afterTop, afterResult, afterGo, descent, afterDescent, unwind, footer, descentBody, nodeChoice, nonempty, afterKind, hashGuard, afterHash, kindChoice, leafBlock, nonleaf, extensionBlock, branchBlock, afterSegment, prefixScope, prefixChoice, extensionFrameScope, extensionPush, branchValue, branchIndexScope, branchFrameScope, branchPush, unwindBody, afterFrameNode, unwindChoice, pop, field, childAddress, remaining, keySuffix, descentTest, unwindTest, Guest.guestFn__mpt_delete_node_body, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> simp

theorem branch_shapes : branchBlock=.ite (.cmp .equal (localVar "level") (localVar "klen")) branchValue branchIndexScope ∧
    branchIndexScope=.dec (ofString "idx") .one (.loadByte keySuffix) branchFrameScope ∧
    branchFrameScope=.decCall (ofString "fr2") .one (ofString "scratch_alloc") [.const 40#64] branchPush ∧
    branchValue=.ite (.cmp .equal (field "node" 168#64) (.const 0#64)) (.assign .local (ofString "res") (localVar "node"))
      (.seq (.store (.op .add [localVar "node",.const 160#64]) (.const 0#64))
        (.seq (.store (.op .add [localVar "node",.const 168#64]) (.const 0#64))
          (.call (some (some (.local,ofString "res"),none)) (ofString "_collapse_branch") [localVar "node"]))) := by
  simp only [body, afterTop, afterResult, afterGo, descent, afterDescent, unwind, footer, descentBody, nodeChoice, nonempty, afterKind, hashGuard, afterHash, kindChoice, leafBlock, nonleaf, extensionBlock, branchBlock, afterSegment, prefixScope, prefixChoice, extensionFrameScope, extensionPush, branchValue, branchIndexScope, branchFrameScope, branchPush, unwindBody, afterFrameNode, unwindChoice, pop, field, childAddress, remaining, keySuffix, descentTest, unwindTest, Guest.guestFn__mpt_delete_node_body, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> simp

theorem unwind_shapes : unwind=.while unwindTest unwindBody ∧
    unwindBody=.dec (ofString "fnode") .one (field "top" 8#64) afterFrameNode ∧ afterFrameNode=.seq unwindChoice pop ∧
    unwindChoice=.ite (.cmp .equal (field "top" 16#64) (.const 2#64))
      (.call (some (some (.local,ofString "res"),none)) (ofString "_delete_ext_finish")
        [localVar "fnode",field "top" 24#64,field "top" 32#64,localVar "res"])
      (.seq (.store (childAddress "fnode" (field "top" 32#64)) (localVar "res"))
        (.call (some (some (.local,ofString "res"),none)) (ofString "_collapse_branch") [localVar "fnode"])) ∧
    pop=.assign .local (ofString "top") (field "top" 0#64) := by
  simp only [body, afterTop, afterResult, afterGo, descent, afterDescent, unwind, footer, descentBody, nodeChoice, nonempty, afterKind, hashGuard, afterHash, kindChoice, leafBlock, nonleaf, extensionBlock, branchBlock, afterSegment, prefixScope, prefixChoice, extensionFrameScope, extensionPush, branchValue, branchIndexScope, branchFrameScope, branchPush, unwindBody, afterFrameNode, unwindChoice, pop, field, childAddress, remaining, keySuffix, descentTest, unwindTest, Guest.guestFn__mpt_delete_node_body, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar] <;> simp

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_mpt_delete_node_body")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 254 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__mpt_delete_node_body) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__mpt_delete_node_body,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.setup_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteBody.descent_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteBody.original_code
