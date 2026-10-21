import InitECandidate.Solver.Headers.HelperProgram
import InitECandidate.Solver.Headers.SliceState

namespace InitECandidate.Solver.Headers.Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform costs of the five unchanged helpers, from the actual current
slice-state invariant and original callee array/index/control bindings. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (controlCell : kind.ternary=true → source.locals.lookup kind.controlName=some (.val (.word control)))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤kind.bodyPrice item.total.toNat := by
  cases kind
  · exact (Field.selected_body_cost source .uint array pointer cursor limit bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell installed).1
  · exact (Field.selected_body_cost source .bytes array pointer cursor limit bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell installed).1
  · exact (Field.selected_body_cost source .raw array pointer cursor limit bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell installed).1
  · exact WordField.body_cost source array pointer cursor limit bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell installed
  · exact U256Field.body_cost source array pointer cursor limit control bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell (controlCell rfl) installed

/-- Each genuine normal original helper return retains the current slice
state and every global, independently of the numerical/hash input contents. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (controlCell : kind.ternary=true → source.locals.lookup kind.controlName=some (.val (.word control)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) := by
  have frame : Rlp.Validation.Arena post cursor limit ∧ Rlp.Validation.Above source post cursor.toNat ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) := by
    cases kind
    · obtain ⟨args,_,_,fits⟩ := Field.selected_arguments source array pointer bytes index items item selected state.itemsAtInput state.records state.arena.domain state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell
      have result:=Field.body_normal_frame source post .uint (Rlp.Slices.itemPointer pointer items index) item.total cursor limit args state.arena fits installed value normal
      exact ⟨result.1,result.2.1,result.2.2.1⟩
    · obtain ⟨args,_,_,fits⟩ := Field.selected_arguments source array pointer bytes index items item selected state.itemsAtInput state.records state.arena.domain state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell
      have result:=Field.body_normal_frame source post .bytes (Rlp.Slices.itemPointer pointer items index) item.total cursor limit args state.arena fits installed value normal
      exact ⟨result.1,result.2.1,result.2.2.1⟩
    · obtain ⟨args,_,_,fits⟩ := Field.selected_arguments source array pointer bytes index items item selected state.itemsAtInput state.records state.arena.domain state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell
      have result:=Field.body_normal_frame source post .raw (Rlp.Slices.itemPointer pointer items index) item.total cursor limit args state.arena fits installed value normal
      exact ⟨result.1,result.2.1,result.2.2.1⟩
    · exact word_normal_frame source post array pointer cursor limit bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell installed value normal
    · exact u256_normal_frame source post array pointer cursor limit control bytes index items item selected state.itemsAtInput state.records state.arena state.arrayArena state.arrayAligned state.inputFits arrayCell indexCell (controlCell rfl) installed value normal
  exact frame

/-- Each genuine normal original helper return retains the current slice
state and every global, independently of the numerical/hash input contents. -/
theorem body_normal_state (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (controlCell : kind.ternary=true → source.locals.lookup kind.controlName=some (.val (.word control)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    SliceState post pointer array cursor limit bytes cutoff items ∧ (∀ key,post.globals.lookup key=source.globals.lookup key) := by
  have frame:=body_normal_frame source post kind array pointer cursor limit control bytes cutoff index items item state selected arrayCell indexCell controlCell installed value normal
  have fields:=Input.evaluation_fields source post kind.body (some (.returned value)) normal
  exact ⟨state.above source post pointer array cursor limit bytes cutoff items frame.1 frame.2.1 fields.1 fields.2.1,frame.2.2⟩

end InitECandidate.Solver.Headers.Helper

#print axioms InitECandidate.Solver.Headers.Helper.body_cost
#print axioms InitECandidate.Solver.Headers.Helper.body_normal_state

#print axioms InitECandidate.Solver.Headers.Helper.body_normal_frame
