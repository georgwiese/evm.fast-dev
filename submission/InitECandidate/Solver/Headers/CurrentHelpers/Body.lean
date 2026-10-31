import InitECandidate.Solver.Headers.HelperSyntax
import InitECandidate.Solver.Headers.CurrentHelpers.State
import InitECandidate.Solver.Headers.CurrentWordMemory
import InitECandidate.Solver.Headers.CurrentU256Memory

namespace InitECandidate.Solver.Headers.CurrentHelpers
open Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def overhead : Kind→Nat | .word=>20 | .u256=>45 | _=>11
def bodyPrice (kind : Kind) (bytes : Nat) : Nat := 60*bytes+overhead kind

/-- Uniform costs of the five unchanged helpers, from the actual current
slice-state invariant and original callee array/index/control bindings. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (controlCell : kind.ternary=true → source.locals.lookup kind.controlName=some (.val (.word control)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤bodyPrice kind item.total.toNat := by
  have row:=Field.selected_arguments source array pointer bytes index items item selected state.itemsAtInput state.records state.arena.domain state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell
  cases kind
  · exact CurrentField.body_cost source .uint (Rlp.Slices.itemPointer pointer items index) item.total row.1 state.arena row.2.2.2 installed
  · exact CurrentField.body_cost source .bytes (Rlp.Slices.itemPointer pointer items index) item.total row.1 state.arena row.2.2.2 installed
  · exact CurrentField.body_cost source .raw (Rlp.Slices.itemPointer pointer items index) item.total row.1 state.arena row.2.2.2 installed
  · exact CurrentWord.body_cost source array pointer bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell installed
  · exact CurrentU256.body_cost source array pointer control bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell (controlCell rfl) installed

end InitECandidate.Solver.Headers.CurrentHelpers

#print axioms InitECandidate.Solver.Headers.CurrentHelpers.body_cost
