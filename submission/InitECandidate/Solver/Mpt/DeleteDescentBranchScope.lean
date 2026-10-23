import InitECandidate.Solver.Mpt.DeleteDescentBranchPush
import InitECandidate.Solver.Mpt.DeleteDescentBranchProgram
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The true query-byte read supplies its range below16; its actual
allocation/push and lexical exit derive the complete next descent model. -/
theorem branch_scope_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (before : model.level.toNat<length.toNat)
    (normal : evaluateHOLFiniteState source branchIndexScope=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  obtain ⟨nibble,small,byteRead⟩:=model.query.span.nibble model.level.toNat before
  have first : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (key+model.level)=some nibble:=by
    simpa [byteAddress] using byteRead
  have read : eval source branchIndex=some (.val (.word (BitVec.ofNat 64 nibble.toNat))):=by
    simp [eval,evalHOLExact,toExact,localVar,branchIndex,keySuffix,model.keyCell,model.levelCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp,first]
  rw [branch_index_shape] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_none_word source target "idx" branchIndex (BitVec.ofNat 64 nibble.toNat) branchFrameScope read normal
  let ready:=model.bind_auxiliary source key length limit nodeLower pathLower property "idx" (BitVec.ofNat 64 nibble.toNat) (by decide)
  obtain ⟨output⟩:=branch_push_output (QueryBranch.bind source "idx" (BitVec.ofNat 64 nibble.toNat)) inner key length limit nodeLower pathLower property ready active tag nibble.toNat small
    (bind_lookup_same _ _ _) before continued
  rw [endpoint]
  exact DescentOutput.restore_auxiliary source inner key length limit nodeLower pathLower property model "idx" (BitVec.ofNat 64 nibble.toNat) (by decide) output

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_scope_output
