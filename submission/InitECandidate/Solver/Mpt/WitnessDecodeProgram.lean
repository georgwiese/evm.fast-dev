import InitECandidate.Solver.Mpt.WitnessStepProgram
import InitECandidate.Solver.Rlp.SlicesSyntax

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def seqFirst : ProgHOL 64→ProgHOL 64 | .seq first _=>first | _=>.skip
def seqRest : ProgHOL 64→ProgHOL 64 | .seq _ rest=>rest | _=>.skip
def decRest : ProgHOL 64→ProgHOL 64 | .dec _ _ _ rest=>rest | _=>.skip
def callRest : ProgHOL 64→ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
def yesBranch : ProgHOL 64→ProgHOL 64 | .ite _ yes _=>yes | _=>.skip
def field (name : String) (index : Nat) : ExpHOL 64:=.rfield index (localVar name)
def fail (error : BitVec 64) : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_fail") [.const error]
def emptyReturn : ProgHOL 64:=.return (.rstruct [.const 0#64,.const 0#64])
def stringBody : ProgHOL 64:=.seq (.ite (.cmp .equal (field "it" 2) (.const 0#64)) emptyReturn .skip) (fail 4#64)
def stringGuard : ProgHOL 64:=.ite (.cmp .equal (field "it" 0) (.const 0#64)) stringBody .skip
def slicesArguments : List (ExpHOL 64):=[field "it" 1,field "it" 2]
def slicesCall : ProgHOL 64:=seqRest (WitnessStep.afterRlp .decode)
def afterSlices : ProgHOL 64:=callRest slicesCall
def afterArray : ProgHOL 64:=decRest afterSlices
def pairBody : ProgHOL 64:=yesBranch (seqFirst afterArray)
def afterPath : ProgHOL 64:=callRest pairBody
def compactCall : ProgHOL 64:=seqRest afterPath
def afterCompact : ProgHOL 64:=callRest compactCall
def leafBody : ProgHOL 64:=yesBranch (seqFirst afterCompact)
def afterValue : ProgHOL 64:=callRest leafBody
def leafAllocate : ProgHOL 64:=seqRest afterValue
def afterLeaf : ProgHOL 64:=callRest leafAllocate
def extensionBody : ProgHOL 64:=seqRest afterCompact
def extensionAllocate : ProgHOL 64:=seqRest extensionBody
def afterExtension : ProgHOL 64:=callRest extensionAllocate
def branchBody : ProgHOL 64:=seqRest afterArray
def branchAllocate : ProgHOL 64:=seqRest branchBody
def branchRecord : ProgHOL 64:=callRest branchAllocate
def afterBranchRecord : ProgHOL 64:=callRest branchRecord
def recordArguments (index : Nat) : List (ExpHOL 64):=
  [.load .one (.op .add [localVar "arr",.panop .mul [.const (BitVec.ofNat 64 index),.const 16#64]]),
    .load .one (.op .add [localVar "arr",.panop .mul [.const (BitVec.ofNat 64 index),.const 16#64],.const 8#64])]

set_option maxRecDepth 100000
theorem suffix_shape : WitnessStep.afterRlp .decode=.seq stringGuard slicesCall := by
  simp only [WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,stringGuard,stringBody,field,emptyReturn,fail,slicesCall,seqRest,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem slices_shape : slicesCall=.decCall (ofString "sl") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") slicesArguments afterSlices := by
  simp only [slicesCall,afterSlices,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,callRest,Rlp.Slices.resultShape,slicesArguments,field,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem after_slices_shape : afterSlices=.dec (ofString "arr") .one (field "sl" 0)
    (.seq (.ite (.cmp .equal (field "sl" 1) (.const 2#64)) pairBody .skip) branchBody) := by
  simp only [afterSlices,afterArray,pairBody,branchBody,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem path_shape : pairBody=.decCall (ofString "pi") Rlp.Item.resultShape (ofString "rlp_item") (recordArguments 0) afterPath := by
  simp only [afterPath,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,recordArguments,Rlp.Item.resultShape,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem after_path_shape : afterPath=.seq (.ite (.cmp .notEqual (field "pi" 0) (.const 0#64)) (fail 5#64) .skip) compactCall := by
  simp only [afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,fail,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem compact_shape : compactCall=.decCall (ofString "cn") (.comb [.one,.one,.one]) (ofString "compact_to_nibbles") [field "pi" 1,field "pi" 2] afterCompact := by
  simp only [afterCompact,afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem after_compact_shape : afterCompact=.seq (.ite (.cmp .notEqual (field "cn" 2) (.const 0#64)) leafBody .skip) extensionBody := by
  simp only [afterCompact,leafBody,extensionBody,afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem value_shape : leafBody=.decCall (ofString "vi") Rlp.Item.resultShape (ofString "rlp_item") (recordArguments 1) afterValue := by
  simp only [afterValue,leafBody,afterCompact,afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,recordArguments,Rlp.Item.resultShape,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem after_value_shape : afterValue=.seq (.ite (.cmp .notEqual (field "vi" 0) (.const 0#64)) (fail 6#64) .skip) leafAllocate := by
  simp only [afterValue,leafAllocate,leafBody,afterCompact,afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,fail,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem leaf_shape : leafAllocate=.decCall (ofString "lf") .one (ofString "node_new_leaf") [field "cn" 0,field "cn" 1,field "vi" 1,field "vi" 2] afterLeaf := by
  simp only [afterLeaf,afterValue,leafAllocate,leafBody,afterCompact,afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem extension_shape : extensionBody=.seq (.ite (.cmp .equal (field "cn" 1) (.const 0#64)) (fail 7#64) .skip)
    (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension) := by
  simp only [extensionBody,extensionAllocate,afterExtension,afterCompact,afterPath,compactCall,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,fail,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem branch_shape : branchBody=.seq (.ite (.cmp .notEqual (field "sl" 1) (.const 17#64)) (fail 4#64) .skip)
    (.decCall (ofString "br") .one (ofString "node_new_branch") [] (.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord)) := by
  simp only [branchBody,branchAllocate,branchRecord,afterBranchRecord,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,field,fail,localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.suffix_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.slices_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_slices_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.path_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_path_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.compact_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_compact_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.value_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_value_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_shape
