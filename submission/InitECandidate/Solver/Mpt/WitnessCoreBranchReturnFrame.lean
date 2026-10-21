import InitECandidate.Solver.Mpt.WitnessCoreBranchPopNormal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual final-branch value and parent stores retain every earlier
word. The genuine parser supplies agreement from source to built; this
lemma accounts only for the real writes after its return and all scopes. -/
theorem branch_finished_memory (source built : PanSemStateFiniteExact 64 Guest.HostMemory) (node previous : BitVec 64)
    (data : WitnessRecord.Description) (header bytes flag : BitVec 64) (occupied : Fin 17)
    (nodeArena : AllocatedBytes.Arena node 176) (query : BitVec 64) (before : query.toNat<node.toNat) :
    (branchFinishedState source built node previous data header bytes flag occupied).memory query=built.memory query := by
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let parsed:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  let entered:=QueryBranch.bind parsed "occ" (BitVec.ofNat 64 occupied.val)
  let valued:=branchValueState entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
  change (metadataState valued node data.pointer data.length previous).memory query=built.memory query
  have upper:=nodeArena.upper
  have away (offset : Nat) (inside : offset+8≤176) : query≠node+BitVec.ofNat 64 offset:=by
    have number : (node+BitVec.ofNat 64 offset).toNat=node.toNat+offset:=byteAddress_toNat node offset (by omega)
    intro same
    have numeric:=congrArg BitVec.toNat same
    rw [number] at numeric
    omega
  rw [metadata_memory valued node data.pointer data.length previous query (away 8 (by decide)) (away 16 (by decide)),
    branch_value_state_memory entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied query
      (away 160 (by decide)) (away 168 (by decide))]
  rfl

/-- The real final value and parent stores also preserve the branch's
tag word, independently of the actual item flag or payload length. -/
theorem branch_finished_tag (source built : PanSemStateFiniteExact 64 Guest.HostMemory) (node previous : BitVec 64)
    (data : WitnessRecord.Description) (header bytes flag : BitVec 64) (occupied : Fin 17) :
    (branchFinishedState source built node previous data header bytes flag occupied).memory node=built.memory node := by
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let parsed:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  let entered:=QueryBranch.bind parsed "occ" (BitVec.ofNat 64 occupied.val)
  let valued:=branchValueState entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
  change (metadataState valued node data.pointer data.length previous).memory node=built.memory node
  have away (offset : BitVec 64) (nonzero : offset≠0#64) : node≠node+offset:=by
    intro same
    have equal : (0#64 : BitVec 64)=offset:=(BitVec.add_right_inj node).mp (by simpa only [BitVec.add_zero] using same)
    exact nonzero equal.symm
  rw [metadata_memory valued node data.pointer data.length previous node (away 8#64 (by decide)) (away 16#64 (by decide)),
    branch_value_state_memory entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied node
      (away 160#64 (by decide)) (away 168#64 (by decide))]
  rfl

/-- After all actual final-value scopes close, unrelated loop locals
retain the caller's bindings; the parser's own locals never escape. -/
theorem branch_finished_other (source built : PanSemStateFiniteExact 64 Guest.HostMemory) (node previous : BitVec 64)
    (data : WitnessRecord.Description) (header bytes flag : BitVec 64) (occupied : Fin 17) (name : String)
    (notArray : ofString "arr2"≠ofString name) (notValue : ofString "bv"≠ofString name) (notOcc : ofString "occ"≠ofString name)
    (notTop : ofString "top"≠ofString name) (notResult : ofString "result"≠ofString name) :
    (branchFinishedState source built node previous data header bytes flag occupied).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let parsed:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  let entered:=QueryBranch.bind parsed "occ" (BitVec.ofNat 64 occupied.val)
  let valued:=branchValueState entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
  change (restore source "arr2" (restore arrayReady "bv" (restore parsed "occ" (metadataState valued node data.pointer data.length previous)))).locals.lookup (ofString name)=source.locals.lookup (ofString name)
  rw [Input.ScalarScope.restore_other _ _ "arr2" name notArray,Input.ScalarScope.restore_other _ _ "bv" name notValue,
    Input.ScalarScope.restore_other _ _ "occ" name notOcc]
  have metadataOther : (metadataState valued node data.pointer data.length previous).locals.lookup (ofString name)=valued.locals.lookup (ofString name):=
    (bind_lookup_other _ "result" name node notResult).trans (bind_lookup_other _ "top" name previous notTop)
  exact metadataOther.trans ((branch_value_state_other entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied name notOcc).trans
    ((bind_lookup_other parsed "occ" name _ notOcc).trans ((Input.CallNormal.continuation_lookup_other arrayReady built "bv" name answer notValue).trans
      (bind_lookup_other source "arr2" name data.array notArray))))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_tag

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_other
