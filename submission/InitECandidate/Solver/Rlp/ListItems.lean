import InitECandidate.Solver.Rlp.HeaderReplay

namespace InitECandidate.Solver.Rlp
open Flapjack PanSemStateFiniteExact

structure ListItem where
  header : BitVec 64
  payload : BitVec 64
  flag : BitVec 64

def ListItem.size (item : ListItem) : Nat := item.header.toNat+item.payload.toNat
def ListItem.total (item : ListItem) : BitVec 64 := item.header+item.payload
def ListItem.valid (item : ListItem) : Prop := Header.Valid item.size (Header.result item.header item.payload item.flag)

/-- Ordered actual item encodings covering exactly the given byte extent.
Each next pointer is the real arithmetic total used by the original loops. -/
inductive ListItems (source : PanSemStateFiniteExact 64 Guest.HostMemory) : BitVec 64 → Nat → List ListItem → Prop where
  | nil (pointer : BitVec 64) : ListItems source pointer 0 []
  | cons (pointer : BitVec 64) (item : ListItem) (bytes : Nat) (items : List ListItem)
      (encoded : Header.Encoded source pointer item.header item.payload item.flag)
      (valid : item.valid) (rest : ListItems source (pointer+item.total) bytes items) :
      ListItems source pointer (item.size+bytes) (item::items)

theorem ListItem.positive (item : ListItem) (valid : item.valid) : 1≤item.size :=
  (Header.Valid.result_fields item.size item.header item.payload item.flag valid).2.1

theorem ListItems.count_le (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (bytes : Nat) (items : List ListItem) (model : ListItems source pointer bytes items) :
    items.length≤bytes := by
  induction model with
  | nil pointer => simp
  | cons pointer item bytes items encoded valid rest ih =>
    have positive := item.positive valid
    simp only [List.length_cons]
    omega

/-- Item provenance survives agreement on exactly the covered input span;
no unused trailing bytes or future parser execution is required. -/
theorem ListItems.transport (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (bytes : Nat) (items : List ListItem) (model : ListItems source pointer bytes items)
    (small : bytes<2^64)
    (agreement : ∀ offset : BitVec 64,offset.toNat<bytes →
      ReadLength.byte source (pointer+offset)=ReadLength.byte target (pointer+offset)) :
    ListItems target pointer bytes items := by
  induction model with
  | nil pointer => exact .nil pointer
  | cons pointer item bytes items encoded valid rest ih =>
    have positive := item.positive valid
    have headNumber : item.total.toNat=item.size := BitVec.toNat_add_of_lt (by change item.size<2^64; omega)
    have headFrame := Header.Encoded.transport source target pointer item.header item.payload item.flag encoded
      (fun offset inside=>agreement offset (by dsimp [ListItem.size] at positive ⊢; omega))
    apply ListItems.cons pointer item bytes items headFrame valid
    apply ih (by omega)
    intro offset inside
    have number : (item.total+offset).toNat=item.size+offset.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [headNumber]; omega),headNumber]
    have frame := agreement (item.total+offset) (by rw [number]; omega)
    simpa only [BitVec.add_assoc] using frame

end InitECandidate.Solver.Rlp

#print axioms InitECandidate.Solver.Rlp.ListItem.positive
#print axioms InitECandidate.Solver.Rlp.ListItems.count_le
#print axioms InitECandidate.Solver.Rlp.ListItems.transport
