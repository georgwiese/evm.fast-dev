import InitECandidate.Solver.Mpt.WitnessBranchChildren
import InitECandidate.Solver.Mpt.WitnessBranchValueView
import InitECandidate.Solver.Mpt.WitnessCoreBranchReturnFrame

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open WitnessRadix.QueryBranch

/-- The final value/metadata writes touch none of the sixteen child
slots. This also accounts for every real scope restoration. -/
theorem branch_finished_field_memory (source built : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node previous : BitVec 64) (data : WitnessRecord.Description) (header bytes flag : BitVec 64) (occupied : Fin 17)
    (query : BitVec 64) (away8 : query≠node+8#64) (away16 : query≠node+16#64)
    (away160 : query≠node+160#64) (away168 : query≠node+168#64) :
    (branchFinishedState source built node previous data header bytes flag occupied).memory query=built.memory query := by
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let parsed:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  let entered:=QueryBranch.bind parsed "occ" (BitVec.ofNat 64 occupied.val)
  let valued:=branchValueState entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
  change (metadataState valued node data.pointer data.length previous).memory query=built.memory query
  rw [metadata_memory valued node data.pointer data.length previous query away8 away16,
    branch_value_state_memory entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied query away160 away168]
  rfl

theorem Children.finished (source built : PanSemStateFiniteExact 64 Guest.HostMemory)
    (valid : BitVec 64 → Prop) (node previous cursor : BitVec 64) (data : WitnessRecord.Description)
    (header bytes flag : BitVec 64) (occupied : Fin 17)
    (children : Children source valid node 16) (arena : AllocatedBytes.Arena node 176)
    (floor : 2713731432≤node.toNat) (below : cursor.toNat≤2713717616)
    (above : Rlp.Validation.Above source built cursor.toNat) :
    Children (branchFinishedState source built node previous data header bytes flag occupied) valid node 16 := by
  apply children.frame source _ valid node 16
  intro index inside
  have number : (byteAddress node (32+8*index)).toNat=node.toNat+(32+8*index) := byteAddress_toNat node _ (by have upper:=arena.upper; omega)
  have distinct (offset : Nat) (small : offset<2^64) (outside : offset<32 ∨ 152<offset) :
      byteAddress node (32+8*index)≠node+BitVec.ofNat 64 offset := by
    intro equal
    have cancelled : BitVec.ofNat 64 (32+8*index)=BitVec.ofNat 64 offset := (BitVec.add_right_inj node).mp equal
    have numeric:=congrArg BitVec.toNat cancelled
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt small] at numeric
    omega
  exact (branch_finished_field_memory source built node previous data header bytes flag occupied _
    (distinct 8 (by decide) (Or.inl (by decide))) (distinct 16 (by decide) (Or.inl (by decide)))
    (distinct 160 (by decide) (Or.inr (by decide))) (distinct 168 (by decide) (Or.inr (by decide)))).trans
    (above _ (by omega))

/-- The completed branch's real value words are bounded input payload or
the retained original empty value, after actual parser and scope frames. -/
def branch_finished_value (source built : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node previous header bytes flag cursor : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17) (item : Rlp.ListItem)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (selected : data.items[16]?=some item) (dbUpper : db.toNat≤33806089496)
    (valid : Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat
      (Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag))
    (empty : EmptyValue source node) (below : cursor.toNat≤2713717616)
    (above : Rlp.Validation.Above source built cursor.toNat) (builtDomain : built.memaddrs=source.memaddrs) :
    let post:=branchFinishedState source built node previous data header bytes flag occupied
    TrieWalk.ValueView post.memory post.memaddrs node 160#64 168#64 1024 (WitnessValue db) := by
  have owned:=view.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have nodeFloor : 2713731432≤node.toNat := by simpa only [payload,WitnessRecord.Payload.startAddress] using view.payloadFloor
  obtain ⟨valueArena,small,lower,before⟩:=branch_value_payload source record db node header bytes flag data index occupied item view payload selected dbUpper valid
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let parsed:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  let entered:=QueryBranch.bind parsed "occ" (BitVec.ofNat 64 occupied.val)
  let valued:=branchValueState entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
  have number160 : (node+160#64).toNat=node.toNat+160 := byteAddress_toNat node 160 (by have upper:=owned.1.upper; omega)
  have number168 : (node+168#64).toNat=node.toNat+168 := byteAddress_toNat node 168 (by have upper:=owned.1.upper; omega)
  have emptyEntered : EmptyValue entered node := ⟨(above _ (by omega)).trans empty.1,(above _ (by omega)).trans empty.2⟩
  have valueView:=branch_value_state_value entered db node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
    (builtDomain.trans view.rows.domain) owned.1 owned.2.1 emptyEntered valueArena small lower before
  let post:=branchFinishedState source built node previous data header bytes flag occupied
  have same (offset : BitVec 64) (away8 : offset≠8#64) (away16 : offset≠16#64) :
      post.memory (node+offset)=valued.memory (node+offset) := by
    change (metadataState valued node data.pointer data.length previous).memory (node+offset)=valued.memory (node+offset)
    exact metadata_memory valued node data.pointer data.length previous _
      (fun equal=>away8 ((BitVec.add_right_inj node).mp equal)) (fun equal=>away16 ((BitVec.add_right_inj node).mp equal))
  exact TrieWalk.ValueView.of_agreement valued.memory post.memory valued.memaddrs post.memaddrs node 160#64 168#64 1024 valueView rfl
    (same 160#64 (by decide) (by decide)) (same 168#64 (by decide) (by decide))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_field_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Children.finished
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_value
