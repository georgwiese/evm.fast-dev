import InitECandidate.Solver.Mpt.WitnessDecodeProgram
import InitECandidate.Solver.Mpt.LocalFieldStores

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang WitnessRadix
open Flapjack.Basis.Pure.MlString

def extensionFields (words : String→BitVec 64) : List LocalFields.Field:=
  [⟨8,.literal 1#64⟩,⟨24,.saved "arr" (words "arr")⟩,⟨48,.saved "p" (words "p")⟩,⟨56,.saved "n" (words "n")⟩,
    ⟨64,.selected "cn" 0 (words "nib")⟩,⟨72,.selected "cn" 1 (words "nlen")⟩]
def branchFields (words : String→BitVec 64) : List LocalFields.Field:=
  [⟨8,.literal 2#64⟩,⟨16,.saved "br" (words "br")⟩,⟨24,.saved "arr" (words "arr")⟩,⟨32,.literal 0#64⟩,⟨40,.literal 0#64⟩,
    ⟨48,.saved "p" (words "p")⟩,⟨56,.saved "n" (words "n")⟩]
def leafFields (words : String→BitVec 64) : List LocalFields.Field:=
  [⟨8,.saved "p" (words "p")⟩,⟨16,.saved "n" (words "n")⟩]
def returnPair (tag : BitVec 64) (name : String) : ProgHOL 64:=.return (.rstruct [.const tag,QueryBranch.localVar name])

set_option maxRecDepth 100000 in
theorem extension_tail_shape (words : String→BitVec 64) :
    afterExtension=LocalFields.program "rec" (extensionFields words) (returnPair 1#64 "rec") := by
  simp only [afterExtension,extensionAllocate,extensionBody,afterCompact,compactCall,afterPath,pairBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,
    LocalFields.program,LocalFields.address,LocalFields.Operand.expression,extensionFields,returnPair,QueryBranch.addConst,QueryBranch.localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
set_option maxRecDepth 100000 in
theorem branch_tail_shape (words : String→BitVec 64) :
    afterBranchRecord=LocalFields.program "rec2" (branchFields words) (returnPair 1#64 "rec2") := by
  simp only [afterBranchRecord,branchRecord,branchAllocate,branchBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,
    LocalFields.program,LocalFields.address,LocalFields.Operand.expression,branchFields,returnPair,QueryBranch.addConst,QueryBranch.localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
set_option maxRecDepth 100000 in
theorem leaf_tail_shape (words : String→BitVec 64) :
    afterLeaf=LocalFields.program "lf" (leafFields words) (returnPair 0#64 "lf") := by
  simp only [afterLeaf,leafAllocate,afterValue,leafBody,afterCompact,compactCall,afterPath,pairBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,
    LocalFields.program,LocalFields.address,LocalFields.Operand.expression,leafFields,returnPair,QueryBranch.addConst,QueryBranch.localVar,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem tails_quiet (code) : Input.QuietClock.Preserves code afterExtension ∧ Input.QuietClock.Preserves code afterBranchRecord ∧ Input.QuietClock.Preserves code afterLeaf := by
  rw [extension_tail_shape (fun _=>0#64),branch_tail_shape (fun _=>0#64),leaf_tail_shape (fun _=>0#64)]
  exact ⟨LocalFields.quiet code _ _ _ (Input.QuietClock.returned code _),LocalFields.quiet code _ _ _ (Input.QuietClock.returned code _),LocalFields.quiet code _ _ _ (Input.QuietClock.returned code _)⟩

theorem extension_geometry (words : String→BitVec 64) :
    ∀ field∈extensionFields words,field.offset+8≤88 ∧ field.offset%8=0 := by simp [extensionFields]
theorem branch_geometry (words : String→BitVec 64) :
    ∀ field∈branchFields words,field.offset+8≤88 ∧ field.offset%8=0 := by simp [branchFields]
theorem leaf_geometry (words : String→BitVec 64) :
    ∀ field∈leafFields words,field.offset+8≤64 ∧ field.offset%8=0 := by simp [leafFields]

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_tail_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_tail_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_tail_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.tails_quiet
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_geometry
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_geometry
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_geometry
