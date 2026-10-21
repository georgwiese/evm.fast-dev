import InitECandidate.Solver.Mpt.WitnessBranchChildren
import InitECandidate.Solver.Mpt.WitnessBranchEmptyValue
import InitECandidate.Solver.Mpt.WitnessCoreStackView
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix

def ChildView (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop) (entry : Entry) : Prop :=
  match entry.data.payload with
  | .extension ..=>True
  | .branch node index _=>Children source valid node index.val ∧ EmptyValue source node

/-- Previously completed slots and still-empty value fields for every
real active branch. Child closure is tied to the current completed registry. -/
def ChildViews (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop) (stack : List Entry) : Prop :=
  ∀ entry∈stack,ChildView source valid entry

theorem ChildViews.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop) : ChildViews source valid [] := by
  intro entry member; cases member

theorem ChildViews.tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop)
    (entry : Entry) (rest : List Entry) (children : ChildViews source valid (entry::rest)) : ChildViews source valid rest :=
  fun current member=>children current (List.mem_cons_of_mem entry member)

/-- Frame only a pending branch's own initialized words below its real
allocation mark, while allowing the completed-node registry to grow. -/
theorem ChildViews.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : BitVec 64 → Prop) (db : BitVec 64) (cursor heap : Nat) (stack : List Entry)
    (view : View source db cursor heap stack) (children : ChildViews source first stack)
    (includes : ∀ child,first child→second child)
    (memory : ∀ entry∈stack,∀ query : BitVec 64,entry.data.payload.startAddress≤query.toNat→query.toNat<entry.mark→
      target.memory query=source.memory query) : ChildViews target second stack := by
  intro entry member
  have current:=children entry member
  have physical:=view.records entry member
  have before:=view.before entry member
  cases payload : entry.data.payload with
  | extension nibbles length=>simp only [ChildView,payload]
  | branch node index occupied=>
    simp only [ChildView,payload] at current ⊢
    have owned:=physical.owned
    simp only [payload,WitnessRecord.Payload.Owned] at owned
    have last : node.toNat+176≤entry.mark := by simpa only [payload,WitnessRecord.Payload.endAddress] using before.2
    have agree (offset : Nat) (inside : offset<176) : target.memory (byteAddress node offset)=source.memory (byteAddress node offset) := by
      have number : (byteAddress node offset).toNat=node.toNat+offset := byteAddress_toNat node offset (by have upper:=owned.1.upper; omega)
      apply memory entry member
      · simpa only [payload,WitnessRecord.Payload.startAddress,number] using Nat.le_add_right node.toNat offset
      · rw [number]; omega
    refine ⟨?_, current.2.frame source target node (agree 160 (by decide)) (agree 168 (by decide))⟩
    apply (current.1.enlarge source first second node index.val includes).frame source target second node index.val
    intro index2 inside
    exact agree (32+8*index2) (by have bound:=index.isLt; omega)

/-- Actual decode/resolve normal memory frames protect every already
completed child slot and empty value in the old active stack. -/
theorem ChildViews.normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : BitVec 64 → Prop) (db heap cursor limit : BitVec 64) (stack : List Entry)
    (view : View source db cursor.toNat heap.toNat stack) (children : ChildViews source first stack)
    (includes : ∀ child,first child→second child) (below : cursor.toNat≤2713717616)
    (frame : WitnessDecode.NormalFrame source target heap cursor limit) : ChildViews target second stack := by
  apply children.frame source target first second db cursor.toNat heap.toNat stack view includes
  intro entry member query lower upper
  have floor:=(view.records entry member).payloadFloor
  have mark:=view.marks entry member
  exact frame.memory query (by omega) (by omega)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ChildViews.frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ChildViews.normal_frame
