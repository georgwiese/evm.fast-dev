import InitECandidate.Solver.Mpt.WitnessCoreLoopProgram

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private def decRest : ProgHOL 64→ProgHOL 64 | .dec _ _ _ rest=>rest | _=>.skip
private def callRest : ProgHOL 64→ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
private def seqFirst : ProgHOL 64→ProgHOL 64 | .seq first _=>first | _=>.skip
private def seqRest : ProgHOL 64→ProgHOL 64 | .seq _ rest=>rest | _=>.skip
private def yesBranch : ProgHOL 64→ProgHOL 64 | .ite _ yes _=>yes | _=>.skip
private def noBranch : ProgHOL 64→ProgHOL 64 | .ite _ _ no=>no | _=>.skip
def readAt (name : String) (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar name,.const offset])
def writeAt (name : String) (offset : BitVec 64) (value : ExpHOL 64) : ProgHOL 64:=.store (.op .add [localVar name,.const offset]) value
def returnFail (code : BitVec 64) : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_fail") [.const code]
def returnField (index : Nat) : ExpHOL 64:=.rfield index (localVar "bv")
def truthy (expression : ExpHOL 64) : ExpHOL 64:=.cmp .notEqual (.const 0#64) expression
def finishReturn : ProgHOL 64:=yesBranch returnBranch
def activeReturn : ProgHOL 64:=noBranch returnBranch
def afterReturnHash : ProgHOL 64:=decRest activeReturn
def cacheReturnHash : ProgHOL 64:=seqFirst afterReturnHash
def returnStages : ProgHOL 64:=seqRest afterReturnHash
def returnExtension : ProgHOL 64:=yesBranch returnStages
def returnBranchNode : ProgHOL 64:=noBranch returnStages
def extensionKindRead : ProgHOL 64:=seqRest returnExtension
def afterExtensionKind : ProgHOL 64:=decRest extensionKindRead
def extensionCreate : ProgHOL 64:=seqRest afterExtensionKind
def afterExtensionCreate : ProgHOL 64:=callRest extensionCreate
def extensionArguments : List (ExpHOL 64):=[readAt "top" 64#64,readAt "top" 72#64,localVar "result"]
def popWith (name : String) : ProgHOL 64:=.seq (.assign .local (ofString "top") (readAt "top" 0#64)) (.assign .local (ofString "result") (localVar name))
def parentMetadata (name : String) : ProgHOL 64:=
  .seq (writeAt name 8#64 (readAt "top" 48#64)) (.seq (writeAt name 16#64 (readAt "top" 56#64)) (popWith name))
def cacheReturnTest : ExpHOL 64:=.op .and
  [truthy (.cmp .notEqual (localVar "hash") (.const 0#64)),truthy (.cmp .notEqual (localVar "result") (.const 0#64))]
def extensionKindTest : ExpHOL 64:=.op .and
  [truthy (.cmp .notEqual (localVar "ck") (.const 3#64)),truthy (.cmp .notEqual (localVar "ck") (.const 0#64))]
def branchIndexRead : ProgHOL 64:=decRest returnBranchNode
def branchChildren : ProgHOL 64:=decRest branchIndexRead
def branchAfterChild : ProgHOL 64:=seqRest branchChildren
def branchAfterOccupancy : ProgHOL 64:=seqRest branchAfterChild
def branchIndexChoice : ProgHOL 64:=seqRest branchAfterOccupancy
def branchAdvance : ProgHOL 64:=yesBranch branchIndexChoice
def branchFinish : ProgHOL 64:=noBranch branchIndexChoice
def branchValueCall : ProgHOL 64:=decRest branchFinish
def afterBranchValue : ProgHOL 64:=callRest branchValueCall
def branchValueBody : ProgHOL 64:=decRest afterBranchValue
def branchValueWrites : ProgHOL 64:=seqFirst branchValueBody
def branchFinishTail : ProgHOL 64:=seqRest branchValueBody
def branchMetadata : ProgHOL 64:=seqRest branchFinishTail
def branchChildAddress : ExpHOL 64:=.op .add [localVar "br",.const 32#64,.panop .mul [localVar "i",.const 8#64]]
def branchOccupancyWrite : ProgHOL 64:=writeAt "top" 40#64 (.op .add [readAt "top" 40#64,.const 1#64])
def branchValueArguments : List (ExpHOL 64):=
  [.load .one (.op .add [localVar "arr2",.panop .mul [.const 16#64,.const 16#64]]),
   .load .one (.op .add [localVar "arr2",.panop .mul [.const 16#64,.const 16#64],.const 8#64])]

local macro "witness_core_return_shape" : tactic =>
  `(tactic| simp only [
    decRest,callRest,seqFirst,seqRest,yesBranch,noBranch,
    readAt,writeAt,returnFail,returnField,truthy,finishReturn,
    activeReturn,afterReturnHash,cacheReturnHash,returnStages,returnExtension,returnBranchNode,
    extensionKindRead,afterExtensionKind,extensionCreate,afterExtensionCreate,extensionArguments,popWith,
    parentMetadata,cacheReturnTest,extensionKindTest,branchIndexRead,branchChildren,branchAfterChild,
    branchAfterOccupancy,branchIndexChoice,branchAdvance,branchFinish,branchValueCall,afterBranchValue,
    branchValueBody,branchValueWrites,branchFinishTail,branchMetadata,branchChildAddress,branchOccupancyWrite,
    branchValueArguments,returnBranch,loopBody,afterLocals,dropDeclarations,body,
    localVar,Guest.Software.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,
    List.map_nil,Option.map_some,Option.map_none])

set_option maxRecDepth 100000
theorem return_shape : returnBranch=.ite (.cmp .equal (localVar "top") (.const 0#64)) finishReturn activeReturn := by witness_core_return_shape
theorem finish_return_shape : finishReturn=.assign .local (ofString "go") (.const 0#64) := by witness_core_return_shape
theorem active_return_shape : activeReturn=.dec (ofString "hash") .one (readAt "top" 80#64) afterReturnHash := by witness_core_return_shape
theorem after_return_hash_shape : afterReturnHash=.seq cacheReturnHash returnStages := by witness_core_return_shape
theorem cache_return_hash_shape : cacheReturnHash=.ite cacheReturnTest (writeAt "result" 24#64 (localVar "hash")) .skip := by witness_core_return_shape
theorem return_stages_shape : returnStages=.ite (.cmp .equal (readAt "top" 8#64) (.const 1#64)) returnExtension returnBranchNode := by witness_core_return_shape
theorem return_extension_shape : returnExtension=.seq (.ite (.cmp .equal (localVar "result") (.const 0#64)) (returnFail 8#64) .skip) extensionKindRead := by witness_core_return_shape
theorem extension_kind_read_shape : extensionKindRead=.dec (ofString "ck") .one (readAt "result" 0#64) afterExtensionKind := by witness_core_return_shape
theorem after_extension_kind_shape : afterExtensionKind=.seq (.ite extensionKindTest (returnFail 8#64) .skip) extensionCreate := by witness_core_return_shape
theorem extension_create_shape : extensionCreate=.decCall (ofString "ex") .one (ofString "node_new_ext") extensionArguments afterExtensionCreate := by witness_core_return_shape
theorem after_extension_create_shape : afterExtensionCreate=parentMetadata "ex" := by witness_core_return_shape
theorem return_branch_node_shape : returnBranchNode=.dec (ofString "br") .one (readAt "top" 16#64) branchIndexRead := by witness_core_return_shape
theorem branch_index_read_shape : branchIndexRead=.dec (ofString "i") .one (readAt "top" 32#64) branchChildren := by witness_core_return_shape
theorem branch_children_shape : branchChildren=.seq (.store branchChildAddress (localVar "result")) branchAfterChild := by witness_core_return_shape
theorem branch_after_child_shape : branchAfterChild=.seq (.ite (.cmp .notEqual (localVar "result") (.const 0#64)) branchOccupancyWrite .skip) branchAfterOccupancy := by witness_core_return_shape
theorem branch_after_occupancy_shape : branchAfterOccupancy=.seq (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])) branchIndexChoice := by witness_core_return_shape
theorem branch_index_choice_shape : branchIndexChoice=.ite (.cmp .less (localVar "i") (.const 16#64)) branchAdvance branchFinish := by witness_core_return_shape
theorem branch_advance_shape : branchAdvance=.seq (writeAt "top" 32#64 (localVar "i"))
    (.seq (.assign .local (ofString "slot") (localVar "i")) (.assign .local (ofString "mode") (.const 2#64))) := by witness_core_return_shape
theorem branch_finish_shape : branchFinish=.dec (ofString "arr2") .one (readAt "top" 24#64) branchValueCall := by witness_core_return_shape
theorem branch_value_call_shape : branchValueCall=.decCall (ofString "bv") (.comb [.one,.one,.one,.one]) (ofString "rlp_item") branchValueArguments afterBranchValue := by witness_core_return_shape
theorem after_branch_value_shape : afterBranchValue=.dec (ofString "occ") .one (readAt "top" 40#64) branchValueBody := by witness_core_return_shape
theorem branch_value_body_shape : branchValueBody=.seq branchValueWrites branchFinishTail := by witness_core_return_shape
theorem branch_value_writes_shape : branchValueWrites=.ite (.cmp .equal (returnField 0) (.const 0#64))
    (.seq (writeAt "br" 160#64 (returnField 1)) (.seq (writeAt "br" 168#64 (returnField 2))
      (.ite (.cmp .notEqual (returnField 2) (.const 0#64)) (.assign .local (ofString "occ") (.op .add [localVar "occ",.const 1#64])) .skip))) .skip := by witness_core_return_shape
theorem branch_finish_tail_shape : branchFinishTail=.seq (.ite (.cmp .lower (localVar "occ") (.const 2#64)) (returnFail 9#64) .skip) branchMetadata := by witness_core_return_shape
theorem branch_metadata_shape : branchMetadata=parentMetadata "br" := by witness_core_return_shape

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.finish_return_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.active_return_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_return_hash_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.cache_return_hash_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_stages_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_extension_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_kind_read_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_extension_kind_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_create_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_extension_create_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_branch_node_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_index_read_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_children_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_after_child_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_after_occupancy_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_index_choice_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_advance_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finish_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_call_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_branch_value_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_body_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_writes_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finish_tail_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_metadata_shape
