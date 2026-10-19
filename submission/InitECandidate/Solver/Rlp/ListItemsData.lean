import InitECandidate.Solver.Rlp.ListItems

namespace InitECandidate.Solver.Rlp
open Flapjack PanSemStateFiniteExact

theorem ListItems.nil_extent (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : Nat)
    (model : ListItems source pointer bytes []) : bytes=0 := by
  cases model
  rfl

theorem ListItems.cons_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : Nat)
    (item : ListItem) (items : List ListItem) (model : ListItems source pointer bytes (item::items)) :
    ∃ remaining,bytes=item.size+remaining ∧ Header.Encoded source pointer item.header item.payload item.flag ∧
      item.valid ∧ ListItems source (pointer+item.total) remaining items := by
  cases model with
  | cons pointer item remaining items encoded valid rest => exact ⟨remaining,rfl,encoded,valid,rest⟩

end InitECandidate.Solver.Rlp

#print axioms InitECandidate.Solver.Rlp.ListItems.nil_extent
#print axioms InitECandidate.Solver.Rlp.ListItems.cons_data
