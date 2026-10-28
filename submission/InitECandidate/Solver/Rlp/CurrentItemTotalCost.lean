import InitECandidate.Solver.Rlp.ItemTotalProgram
import InitECandidate.Solver.Rlp.CurrentValidation.WrapperCall
import InitECandidate.Solver.Rlp.HeaderValidCost

namespace InitECandidate.Solver.Rlp.CurrentItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- A real byte-string item runs no nested validator. This retains the
zero-cost source continuation needed for later list byte-budget composition. -/
theorem flat_after_header_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header payload : BitVec 64)
    (cell : source.locals.lookup (ofString "h")=some (Header.result header payload 0#64)) :
    source.clock-(evaluateHOLFiniteState source ItemTotal.afterHeader).2.clock≤0 := by
  have front : source.clock-(evaluateHOLFiniteState source ItemTotal.check).2.clock≤0 := by
    rw [ItemTotal.check_evaluate source header payload 0#64 cell,if_neg (by simp),evaluateHOLFiniteState_skip]
    change source.clock-source.clock≤0
    omega
  exact ClockCost.sequence_current source ItemTotal.check (.return ItemTotal.total) 0 0 front (ClockCost.returned source.code _)

theorem after_header_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+header.toNat+payload.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source ItemTotal.afterHeader).2.clock≤14*(payload.toNat+1)+5 := by
  have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  have front : source.clock-(evaluateHOLFiniteState source ItemTotal.check).2.clock≤14*(payload.toNat+1)+5 := by
    rw [ItemTotal.check_evaluate source header payload flag headerCell]
    by_cases zero : flag=0#64
    · rw [if_neg (not_not_intro zero),evaluateHOLFiniteState_skip]
      change source.clock-source.clock≤_
      omega
    · rw [if_pos zero]
      exact CurrentValidate.call_cost source (pointer+header) payload arena (by rw [number]; exact fits) (some none) ItemTotal.payloadArguments
        (ItemTotal.payload_arguments source pointer header payload flag pointerCell headerCell)
  exact ClockCost.sequence_current source ItemTotal.check (.return ItemTotal.total) (14*(payload.toNat+1)+5) 0 front (ClockCost.returned source.code _)

/-- Complete unchanged rlp_item_total, using the real initialized scratch
arena and actual validated header extent. All stopped outcomes are included;
no mapped scratch or future successful validator is assumed. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source ItemTotal.body).2.clock≤14*length.toNat+30 := by
  rw [ItemTotal.body_shape]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) ItemTotal.arguments=some (Header.values pointer length) := by
    simp [ItemTotal.arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  have paid:=Header.scoped_valid_cost source pointer length "h" ItemTotal.arguments ItemTotal.afterHeader (14*(length.toNat+1)+5) args arena.code
    (by intro spent answer valid
        obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩ := valid
        rw [same]
        let ready:=setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-spent}
        have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
          simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "h"≠ofString "p" from by decide] using pointerCell
        have readyHeader : ready.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
          simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
        have allowance:=after_header_cost ready pointer header payload flag readyPointer readyHeader (arena.of_frame rfl) (by omega)
        change source.clock-spent-(evaluateHOLFiniteState ready ItemTotal.afterHeader).2.clock≤_ at allowance ⊢
        omega)
  have arithmetic : ∀ n : Nat,11+(14*(n+1)+5)≤14*n+30 := by intro n; omega
  exact Nat.le_trans paid (arithmetic length.toNat)

end InitECandidate.Solver.Rlp.CurrentItemTotal

#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.flat_after_header_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.after_header_cost
#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.body_cost
