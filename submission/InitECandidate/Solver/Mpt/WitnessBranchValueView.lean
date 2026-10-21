import InitECandidate.Solver.Mpt.WitnessCoreBranchValueStores
import InitECandidate.Solver.Mpt.TrieWalkValueAgreement
import InitECandidate.Solver.Rlp.ItemFrameTrace

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

def WitnessValue (db pointer length : BitVec 64) : Prop :=
  length=0#64 ∨ (2713731432≤pointer.toNat ∧ pointer.toNat+length.toNat≤db.toNat)

/-- Before the last row, the branch's original value words remain zero. -/
def EmptyValue (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) : Prop :=
  source.memory (node+160#64)=.word 0#64 ∧ source.memory (node+168#64)=.word 0#64

theorem EmptyValue.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (empty : EmptyValue source node)
    (pointer : target.memory (node+160#64)=source.memory (node+160#64))
    (length : target.memory (node+168#64)=source.memory (node+168#64)) : EmptyValue target node :=
  ⟨pointer.trans empty.1,length.trans empty.2⟩

/-- The real seventeenth row and actual RLP item result locate the value
inside the same bounded original parent input, before the node database. -/
theorem branch_value_payload (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node header bytes flag : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17) (item : Rlp.ListItem)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (selected : data.items[16]?=some item) (dbUpper : db.toNat≤33806089496)
    (valid : Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat
      (Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag)) :
    let pointer:=Rlp.Slices.itemPointer data.listPointer data.items 16+header
    AllocatedBytes.Arena pointer bytes.toNat ∧ bytes.toNat≤1024 ∧
      2713731432≤pointer.toNat ∧ pointer.toNat+bytes.toNat≤db.toNat := by
  obtain ⟨positive,small,first,last⟩ := view.rows.intervals 16 item selected
  obtain ⟨headerSmall,totalPositive,totalBound,binary,listHeader⟩ := valid.result_fields _ header bytes flag item.total.toNat
  have parentBefore:=view.parentBeforeDb
  have parentLower:=view.parentLower
  have listLower:=view.payloadLower
  have listUpper:=view.payloadUpper
  have parentSmall:=view.parentBound
  have pointerNumber : (Rlp.Slices.itemPointer data.listPointer data.items 16+header).toNat=
      (Rlp.Slices.itemPointer data.listPointer data.items 16).toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  dsimp only
  rw [pointerNumber]
  exact ⟨⟨by omega,by omega⟩,by omega,by omega,by omega⟩

/-- The actual flag0 writes expose the row's payload. A list-valued row
retains the original zero value; no fictitious mapped empty byte is read. -/
def branch_value_state_value (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db node pointer header bytes flag : BitVec 64) (occupied : Fin 17)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0)
    (empty : EmptyValue source node)
    (valueArena : AllocatedBytes.Arena (pointer+header) bytes.toNat) (small : bytes.toNat≤1024)
    (lower : 2713731432≤(pointer+header).toNat) (before : (pointer+header).toNat+bytes.toNat≤db.toNat) :
    TrieWalk.ValueView (branchValueState source node pointer header bytes flag occupied).memory
      (branchValueState source node pointer header bytes flag occupied).memaddrs node 160#64 168#64 1024 (WitnessValue db) := by
  let target:=branchValueState source node pointer header bytes flag occupied
  have domainEq : target.memaddrs=source.memaddrs := by
    unfold target branchValueState; split; split <;> rfl; rfl
  have pointerMapped : target.memaddrs (node+160#64) := by
    rw [domainEq]
    exact AllocatedBytes.word_mapped source node 176 160 domain arena (by decide) aligned (by decide)
  have lengthMapped : target.memaddrs (node+168#64) := by
    rw [domainEq]
    exact AllocatedBytes.word_mapped source node 176 168 domain arena (by decide) aligned (by decide)
  by_cases scalar : flag=0#64
  · have pointerStored : target.memory (node+160#64)=.word (pointer+header) := by
      have away : node+160#64≠node+168#64 := by
        intro equal
        exact (by decide : (160#64 : BitVec 64)≠168#64) ((BitVec.add_right_inj node).mp equal)
      unfold target branchValueState
      split
      · split <;> simp [QueryBranch.bind,setVarHOLFinite,StoreWord.put,away]
      · contradiction
    have lengthStored : target.memory (node+168#64)=.word bytes := by
      unfold target branchValueState
      split
      · split <;> simp [QueryBranch.bind,setVarHOLFinite,StoreWord.put]
      · contradiction
    exact ⟨pointer+header,bytes,pointerMapped,pointerStored,lengthMapped,lengthStored,
      ⟨small,by have upper:=valueArena.upper; omega,by
        intro offset inside
        rw [domainEq]
        exact AllocatedBytes.byte_mapped source (pointer+header) bytes.toNat offset domain valueArena inside⟩,
      Or.inr ⟨lower,before⟩⟩
  · have same : target=source := by unfold target branchValueState; rw [if_neg scalar]
    refine ⟨0#64,0#64,pointerMapped,?_,lengthMapped,?_,⟨by decide,by decide,?_⟩,Or.inl rfl⟩
    · change target.memory (node+160#64)=_; rw [same]; exact empty.1
    · change target.memory (node+168#64)=_; rw [same]; exact empty.2
    · intro offset inside; change offset<0 at inside; omega

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_payload
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_state_value
