import InitECandidate.Solver.Headers.FieldRowArguments
import InitECandidate.Solver.Headers.FieldCost

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A complete original field helper is linear in the actual selected row;
its row also has the enclosing header's real byte bound. -/
theorem selected_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (selected : items[index]?=some item) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (arena : Rlp.Validation.Arena source cursor limit) (allocation : AllocatedBytes.Arena array (16*items.length))
    (arrayAligned : array.toNat%8=0) (fits : pointer.toNat+bytes<2^64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤60*item.total.toNat+42 ∧
      source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤60*bytes+42 := by
  obtain ⟨args,positive,bounded,itemFits⟩ := selected_arguments source array pointer bytes index items item selected model records arena.domain allocation arrayAligned fits arrayCell indexCell
  have price := body_cost source kind (Rlp.Slices.itemPointer pointer items index) item.total cursor limit args arena itemFits installed
  exact ⟨price,price.trans (by omega)⟩

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.selected_body_cost
