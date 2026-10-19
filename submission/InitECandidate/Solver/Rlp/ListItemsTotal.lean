import InitECandidate.Solver.Rlp.ListItems

namespace InitECandidate.Solver.Rlp
open Flapjack PanSemStateFiniteExact

theorem ListItems.total_size (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (bytes : Nat) (items : List ListItem) (model : ListItems source pointer bytes items) : (items.map ListItem.size).sum=bytes := by
  induction model with
  | nil pointer => rfl
  | cons pointer item bytes items encoded valid rest ih =>
    simp only [List.map_cons,List.sum_cons,ih]

end InitECandidate.Solver.Rlp

#print axioms InitECandidate.Solver.Rlp.ListItems.total_size
