import InitECandidate.Solver.Mpt.NodeRefLenCall
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.Software.guestFn__node_rlp_finish with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "fr",.one),(ofString "node",.one)]
def afterTag : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterPayload : ProgHOL 64:=match afterTag with | .dec _ _ _ rest=>rest | _=>.skip
def afterBuffer : ProgHOL 64:=match afterPayload with | .dec _ _ _ rest=>rest | _=>.skip
def afterLength : ProgHOL 64:=match afterBuffer with | .dec _ _ _ rest=>rest | _=>.skip
def afterExtension : ProgHOL 64:=match afterLength with | .seq _ rest=>rest | _=>.skip
def branchChoice : ProgHOL 64:=match afterExtension with | .seq first _=>first | _=>.skip
def branchScope : ProgHOL 64:=match branchChoice with | .ite _ yes _=>yes | _=>.skip
def scanAndAfter : ProgHOL 64:=match branchScope with | .dec _ _ _ rest=>rest | _=>.skip
def scanLoop : ProgHOL 64:=match scanAndAfter with | .seq first _=>first | _=>.skip
def afterScan : ProgHOL 64:=match scanAndAfter with | .seq _ rest=>rest | _=>.skip
def scanBody : ProgHOL 64:=match scanLoop with | .while _ rest=>rest | _=>.skip
def scanTest : ExpHOL 64:=.cmp .less (localVar "i") (.const 16#64)
def childArguments : List (ExpHOL 64):=[.load .one (.op .add [localVar "node",.const 32#64,.panop .mul [localVar "i",.const 8#64]])]
def addLength : ProgHOL 64:=.assign .local (ofString "payload") (.op .add [localVar "payload",localVar "rl2"])
def advance : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def valueArguments : List (ExpHOL 64):=[.load .one (.op .add [localVar "node",.const 160#64]),.load .one (.op .add [localVar "node",.const 168#64])]
def addValue : ProgHOL 64:=.assign .local (ofString "payload") (.op .add [localVar "payload",localVar "vl2"])

def allocationScope : ProgHOL 64:=match afterExtension with | .seq _ rest=>rest | _=>.skip
def afterHeaderSize : ProgHOL 64:=match allocationScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match afterHeaderSize with | .decCall _ _ _ _ rest=>rest | _=>.skip
def headerCommand : ProgHOL 64:=match afterAllocation with | .seq first _=>first | _=>.skip
def afterHeaderWrite : ProgHOL 64:=match afterAllocation with | .seq _ rest=>rest | _=>.skip
def writerTail : ProgHOL 64:=match afterHeaderWrite with | .dec _ _ _ rest=>rest | _=>.skip
def allocationArguments : List (ExpHOL 64):=[.op .add [localVar "hl",localVar "payload"]]
def headerArguments : List (ExpHOL 64):=[localVar "buf",localVar "payload"]
def bufferTrace : List Input.CallPrefix.Action:=[
  .scoped (ofString "hl") .one (ofString "rlp_list_header_len") [localVar "payload"],
  .scoped (ofString "buf") .one (ofString "alloc") allocationArguments,
  .command (.call (some (none,none)) (ofString "rlp_encode_list_header") headerArguments),
  .declare (ofString "off") .one (localVar "hl")]

set_option maxRecDepth 100000 in
theorem buffer_shape : allocationScope=Input.CallPrefix.program bufferTrace writerTail ∧
    afterExtension=.seq branchChoice allocationScope := by
  simp only [allocationScope,afterHeaderSize,afterAllocation,headerCommand,afterHeaderWrite,writerTail,
    afterExtension,branchChoice,afterLength,afterBuffer,afterPayload,afterTag,body,bufferTrace,allocationArguments,headerArguments,
    Input.CallPrefix.program,Guest.Software.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  trivial

def writeChoice : ProgHOL 64:=match writerTail with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match writerTail with | .seq _ rest=>rest | _=>.skip
def pathWriteScope : ProgHOL 64:=match writeChoice with | .ite _ yes _=>yes | _=>.skip
def branchWriteScope : ProgHOL 64:=match writeChoice with | .ite _ _ no=>no | _=>.skip
def writesAndValue : ProgHOL 64:=match branchWriteScope with | .dec _ _ _ rest=>rest | _=>.skip
def writeLoop : ProgHOL 64:=match writesAndValue with | .seq first _=>first | _=>.skip
def afterWrites : ProgHOL 64:=match writesAndValue with | .seq _ rest=>rest | _=>.skip
def writeBody : ProgHOL 64:=match writeLoop with | .while _ rest=>rest | _=>.skip
def writeTest : ExpHOL 64:=.cmp .less (localVar "j") (.const 16#64)
def writeChildArguments : List (ExpHOL 64):=[.load .one (.op .add [localVar "node",.const 32#64,.panop .mul [localVar "j",.const 8#64]]),.op .add [localVar "buf",localVar "off"]]
def addWritten : ProgHOL 64:=.assign .local (ofString "off") (.op .add [localVar "off",localVar "w4"])
def writeAdvance : ProgHOL 64:=.assign .local (ofString "j") (.op .add [localVar "j",.const 1#64])

set_option maxRecDepth 100000 in
theorem write_shapes : writerTail=.seq writeChoice footer ∧
    writeChoice=.ite (.cmp .notEqual (localVar "k") (.const 3#64)) pathWriteScope branchWriteScope ∧
    branchWriteScope=.dec (ofString "j") .one (.const 0#64) (.seq writeLoop afterWrites) ∧
    writeLoop=.while writeTest writeBody ∧
    writeBody=.decCall (ofString "w4") .one (ofString "node_write_ref") writeChildArguments (.seq addWritten writeAdvance) := by
  simp only [writeChoice,footer,pathWriteScope,branchWriteScope,writesAndValue,writeLoop,afterWrites,writeBody,writeTest,
    writeChildArguments,addWritten,writeAdvance,writerTail,afterHeaderWrite,afterAllocation,afterHeaderSize,allocationScope,
    afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,Guest.Software.guestFn__node_rlp_finish,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  trivial


def writeValueArguments : List (ExpHOL 64):=[.op .add [localVar "buf",localVar "off"],
  .load .one (.op .add [localVar "node",.const 160#64]),.load .one (.op .add [localVar "node",.const 168#64])]
def addValueWritten : ProgHOL 64:=.assign .local (ofString "off") (.op .add [localVar "off",localVar "w5"])

set_option maxRecDepth 100000 in
theorem write_value_shape : afterWrites=.decCall (ofString "w5") .one (ofString "rlp_encode_bytes") writeValueArguments addValueWritten := by
  simp only [afterWrites,writesAndValue,branchWriteScope,writeChoice,writerTail,afterHeaderWrite,afterAllocation,afterHeaderSize,allocationScope,
    afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,writeValueArguments,addValueWritten,
    Guest.Software.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem footer_shape : footer=.seq (.store (.op .add [localVar "node",.const 8#64]) (localVar "buf"))
    (.seq (.store (.op .add [localVar "node",.const 16#64]) (localVar "off")) (.return (.const 0#64))) := by
  simp only [footer,writerTail,afterHeaderWrite,afterAllocation,afterHeaderSize,allocationScope,
    afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,
    Guest.Software.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

set_option maxRecDepth 100000 in
theorem scan_shapes : scanLoop=.while scanTest scanBody ∧
    scanBody=.decCall (ofString "rl2") .one (ofString "node_ref_len") childArguments (.seq addLength advance) ∧
    branchChoice=.ite (.cmp .equal (localVar "k") (.const 3#64)) (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)) .skip := by
  simp only [scanLoop,scanTest,scanBody,scanAndAfter,afterScan,branchScope,branchChoice,afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,
    Guest.Software.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,
    childArguments,addLength,advance,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem after_scan_shape : afterScan=.decCall (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments addValue := by
  simp only [afterScan,scanAndAfter,branchScope,branchChoice,afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,
    Guest.Software.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,valueArguments,addValue,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_node_rlp_finish")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 256 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__node_rlp_finish) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn__node_rlp_finish,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked


def entryField (name : String) (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar name,.const offset])
def entryTrace : List Input.CallPrefix.Action:=[
  .declare (ofString "k") .one (entryField "node" 0#64),
  .declare (ofString "payload") .one (entryField "fr" 40#64),
  .declare (ofString "cbuf") .one (entryField "fr" 24#64),
  .declare (ofString "clen") .one (entryField "fr" 32#64)]
def extensionChoice : ProgHOL 64:=match afterLength with | .seq first _=>first | _=>.skip
def extensionScope : ProgHOL 64:=match extensionChoice with | .ite _ yes _=>yes | _=>.skip

set_option maxRecDepth 100000 in
theorem entry_shapes : body=Input.CallPrefix.program entryTrace afterLength ∧
    afterLength=.seq extensionChoice afterExtension ∧
    extensionChoice=.ite (.cmp .equal (localVar "k") (.const 2#64)) extensionScope .skip := by
  simp only [entryField,entryTrace,extensionChoice,extensionScope,Input.CallPrefix.program,afterExtension,afterLength,afterBuffer,afterPayload,afterTag,body,
    Guest.Software.guestFn__node_rlp_finish,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  trivial

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_shapes
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.after_scan_shape
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.original_code

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.buffer_shape

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_shapes

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.write_value_shape
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.footer_shape

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.entry_shapes
