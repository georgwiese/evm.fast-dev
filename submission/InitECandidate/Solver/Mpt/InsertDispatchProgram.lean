import InitECandidate.Solver.Mpt.InsertEmptyChoice
import InitECandidate.Solver.Mpt.InsertEmptyFinish

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterKind : ProgHOL 64:=match nonemptyChoice with | .dec _ _ _ rest=>rest | _=>.skip
def hashGuard : ProgHOL 64:=match afterKind with | .seq first _=>first | _=>.skip
def afterHash : ProgHOL 64:=match afterKind with | .seq _ rest=>rest | _=>.skip
def invalidateCall : ProgHOL 64:=match afterHash with | .seq first _=>first | _=>.skip
def kindChoice : ProgHOL 64:=match afterHash with | .seq _ rest=>rest | _=>.skip
def insertLeafCall : ProgHOL 64:=match kindChoice with | .ite _ yes _=>yes | _=>.skip
def extensionChoice : ProgHOL 64:=match kindChoice with | .ite _ _ no=>no | _=>.skip
def extensionScope : ProgHOL 64:=match extensionChoice with | .ite _ yes _=>yes | _=>.skip
def branchChoice : ProgHOL 64:=match extensionChoice with | .ite _ _ no=>no | _=>.skip
def extensionLengthScope : ProgHOL 64:=match extensionScope with | .dec _ _ _ rest=>rest | _=>.skip
def extensionPrefixScope : ProgHOL 64:=match extensionLengthScope with | .dec _ _ _ rest=>rest | _=>.skip
def extensionPrefixChoice : ProgHOL 64:=match extensionPrefixScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def extensionDescend : ProgHOL 64:=match extensionPrefixChoice with | .ite _ yes _=>yes | _=>.skip
def extensionSplitScope : ProgHOL 64:=match extensionPrefixChoice with | .ite _ _ no=>no | _=>.skip
def extensionSplitChoice : ProgHOL 64:=match extensionSplitScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def extensionMakeCall : ProgHOL 64:=match extensionSplitChoice with | .ite _ yes _=>yes | _=>.skip
def extensionBranchAssign : ProgHOL 64:=match extensionSplitChoice with | .ite _ _ no=>no | _=>.skip
def branchValue : ProgHOL 64:=match branchChoice with | .ite _ yes _=>yes | _=>.skip
def branchDescendScope : ProgHOL 64:=match branchChoice with | .ite _ _ no=>no | _=>.skip
def branchDescend : ProgHOL 64:=match branchDescendScope with | .dec _ _ _ rest=>rest | _=>.skip
def nodeFieldExpression (offset : BitVec 64) : ExpHOL 64:=.load .one (addConst (localVar "node") offset)
def queryPointer : ExpHOL 64:=.op .add [localVar "key",localVar "level"]
def queryLength : ExpHOL 64:=.op .sub [localVar "klen",localVar "level"]
def insertLeafArguments : List (ExpHOL 64):=[localVar "node",queryPointer,queryLength,localVar "vptr",localVar "vlen"]
def splitArguments : List (ExpHOL 64):=insertLeafArguments++[localVar "pl"]
def prefixArguments : List (ExpHOL 64):=[localVar "seg",localVar "sl",queryPointer,queryLength]
def extensionArguments : List (ExpHOL 64):=[localVar "seg",localVar "pl",localVar "br"]
def branchIndex : ExpHOL 64:=.loadByte queryPointer
def branchChildAddress : ExpHOL 64:=.op .add [localVar "node",.const 32#64,.panop .mul [localVar "idx",.const 8#64]]

set_option maxRecDepth 100000 in
theorem dispatch_shapes : nonemptyChoice=.dec (ofString "k") .one (nodeFieldExpression 0#64) afterKind ∧
    afterKind=.seq hashGuard afterHash ∧ afterHash=.seq invalidateCall kindChoice ∧
    hashGuard=.ite (.cmp .equal (localVar "k") (.const 0#64)) (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]) .skip ∧
    invalidateCall=.call (some (none,none)) (ofString "node_invalidate") [localVar "node"] ∧
    kindChoice=.ite (.cmp .equal (localVar "k") (.const 1#64)) insertLeafCall extensionChoice ∧
    insertLeafCall=.call (some (some (.local,ofString "r"),none)) (ofString "_insert_into_leaf") insertLeafArguments ∧
    extensionChoice=.ite (.cmp .equal (localVar "k") (.const 2#64)) extensionScope branchChoice := by
  simp only [afterKind,
    hashGuard,
    afterHash,
    invalidateCall,
    kindChoice,
    insertLeafCall,
    extensionChoice,
    extensionScope,
    branchChoice,
    nodeFieldExpression,
    queryPointer,
    queryLength,
    insertLeafArguments,
    nonemptyChoice,
    nodeChoice,
    afterGo,
    afterNextLevel,
    afterNextSlot,
    afterNextNode,
    afterR,
    loopBody,
    loop,
    loopAndAfter,
    afterSlot,
    afterResult,
    body,
    Guest.guestFn__mpt_insert_node,
    progToHOL,
    expToHOL,
    shapeToHOL,
    List.map_cons,
    List.map_nil,
    Option.map_none,
    Option.map_some,
    localVar,
    addConst]; simp

set_option maxRecDepth 100000 in
theorem extension_shapes : extensionScope=.dec (ofString "seg") .one (nodeFieldExpression 32#64) extensionLengthScope ∧
    extensionLengthScope=.dec (ofString "sl") .one (nodeFieldExpression 40#64) extensionPrefixScope ∧
    extensionPrefixScope=.decCall (ofString "pl") .one (ofString "common_prefix_length") prefixArguments extensionPrefixChoice ∧
    extensionPrefixChoice=.ite (.cmp .equal (localVar "pl") (localVar "sl")) extensionDescend extensionSplitScope ∧
    extensionSplitScope=.decCall (ofString "br") .one (ofString "_split_extension") splitArguments extensionSplitChoice ∧
    extensionSplitChoice=.ite (.cmp .lower (.const 0#64) (localVar "pl")) extensionMakeCall extensionBranchAssign ∧
    extensionMakeCall=.call (some (some (.local,ofString "r"),none)) (ofString "node_new_ext") extensionArguments ∧
    extensionBranchAssign=.assign .local (ofString "r") (localVar "br") := by
  simp only [afterKind,
    afterHash,
    kindChoice,
    extensionChoice,
    extensionScope,
    extensionLengthScope,
    extensionPrefixScope,
    extensionPrefixChoice,
    extensionDescend,
    extensionSplitScope,
    extensionSplitChoice,
    extensionMakeCall,
    extensionBranchAssign,
    nodeFieldExpression,
    queryPointer,
    queryLength,
    insertLeafArguments,
    splitArguments,
    prefixArguments,
    extensionArguments,
    nonemptyChoice,
    nodeChoice,
    afterGo,
    afterNextLevel,
    afterNextSlot,
    afterNextNode,
    afterR,
    loopBody,
    loop,
    loopAndAfter,
    afterSlot,
    afterResult,
    body,
    Guest.guestFn__mpt_insert_node,
    progToHOL,
    expToHOL,
    shapeToHOL,
    List.map_cons,
    List.map_nil,
    Option.map_none,
    Option.map_some,
    localVar,
    addConst]; simp

set_option maxRecDepth 100000 in
theorem branch_shapes : branchChoice=.ite (.cmp .equal (localVar "level") (localVar "klen")) branchValue branchDescendScope ∧
    branchValue=.seq (.store (addConst (localVar "node") 160#64) (localVar "vptr"))
      (.seq (.store (addConst (localVar "node") 168#64) (localVar "vlen")) (.assign .local (ofString "r") (localVar "node"))) ∧
    branchDescendScope=.dec (ofString "idx") .one branchIndex branchDescend ∧
    branchDescend=.seq (.assign .local (ofString "r") (localVar "node"))
      (.seq (.assign .local (ofString "next_node") (.load .one branchChildAddress))
      (.seq (.assign .local (ofString "next_slot") branchChildAddress)
      (.seq (.assign .local (ofString "next_level") (.op .add [localVar "level",.const 1#64]))
        (.assign .local (ofString "go") (.const 1#64))))) := by
  simp only [afterKind,
    afterHash,
    kindChoice,
    extensionChoice,
    branchChoice,
    branchValue,
    branchDescendScope,
    branchDescend,
    queryPointer,
    branchIndex,
    branchChildAddress,
    nonemptyChoice,
    nodeChoice,
    afterGo,
    afterNextLevel,
    afterNextSlot,
    afterNextNode,
    afterR,
    loopBody,
    loop,
    loopAndAfter,
    afterSlot,
    afterResult,
    body,
    Guest.guestFn__mpt_insert_node,
    progToHOL,
    expToHOL,
    shapeToHOL,
    List.map_cons,
    List.map_nil,
    Option.map_none,
    Option.map_some,
    localVar,
    addConst]; simp

set_option maxRecDepth 100000 in
theorem extension_descend_shape : extensionDescend=.seq (.assign .local (ofString "r") (localVar "node"))
      (.seq (.assign .local (ofString "next_node") (nodeFieldExpression 48#64))
      (.seq (.assign .local (ofString "next_slot") (addConst (localVar "node") 48#64))
      (.seq (.assign .local (ofString "next_level") (.op .add [localVar "level",localVar "pl"]))
        (.assign .local (ofString "go") (.const 1#64))))) := by
  simp only [afterKind,
    afterHash,
    kindChoice,
    extensionChoice,
    extensionScope,
    extensionLengthScope,
    extensionPrefixScope,
    extensionPrefixChoice,
    extensionDescend,
    nodeFieldExpression,
    nonemptyChoice,
    nodeChoice,
    afterGo,
    afterNextLevel,
    afterNextSlot,
    afterNextNode,
    afterR,
    loopBody,
    loop,
    loopAndAfter,
    afterSlot,
    afterResult,
    body,
    Guest.guestFn__mpt_insert_node,
    progToHOL,
    expToHOL,
    shapeToHOL,
    List.map_cons,
    List.map_nil,
    Option.map_none,
    Option.map_some,
    localVar,
    addConst]

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.dispatch_shapes

#print axioms InitECandidate.Solver.Mpt.Insert.extension_shapes

#print axioms InitECandidate.Solver.Mpt.Insert.branch_shapes

#print axioms InitECandidate.Solver.Mpt.Insert.extension_descend_shape
