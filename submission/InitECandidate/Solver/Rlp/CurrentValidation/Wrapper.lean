import InitECandidate.Solver.Rlp.CurrentValidation.CallCost
import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.ClockCostCaught

namespace InitECandidate.Solver.Rlp.CurrentValidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_rlp_validate_items with | .function fn=>progToHOL fn.body | _=>.skip
def release : ProgHOL 64 := .call (some (none,none)) (ofString "scratch_release") [localVar "mark"]
def handler : ProgHOL 64 := .seq release (.raise (ofString "RlpErr") (localVar "e"))
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def caught : ProgHOL 64 := .call (some (none,some (ofString "RlpErr",ofString "e",handler))) (ofString "_rlp_validate_items_body") arguments
def afterError : ProgHOL 64 := .seq caught (.seq release (.return (.const 0#64)))
def afterMark : ProgHOL 64 := .dec (ofString "e") .one (.const 0#64) afterError

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark := by
  simp only [body,afterMark,afterError,caught,handler,release,arguments,localVar,Guest.Software.guestFn_rlp_validate_items,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_validate_items")=some (Header.formals,body,.one) := by
  have found:=OriginalCode.indexed code installed 99 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_rlp_validate_items) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,
    Guest.Software.guestFn_rlp_validate_items,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using found

theorem handler_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code handler 1 :=
  ClockCost.sequence code _ _ 1 0 (Arenas.Scratch.release_call_price code installed _) (ClockCost.raised code _ _)

theorem caught_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source caught).2.clock≤14*(length.toNat+1)+2 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "_rlp_validate_items_body") Validation.body .one pointer length (Validation.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  have nextArena : CurrentStartup.ArenaState (callEntryStateHOLFinite source callee) := arena.of_frame rfl
  exact ClockCost.caught_current source (ofString "_rlp_validate_items_body") arguments _ Validation.body callee .one (ofString "RlpErr") (ofString "e") handler (14*(length.toNat+1)) 1 args called
    (CurrentValidation.body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal nextArena fits) (handler_price source.code arena.code)

/-- Whole unchanged public RLP validator, including its actual saved mark,
caught RLP error release/raise and normal release/return. Actual below-domain
scratch initialization suffices; all stopped outcomes are included. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤14*(length.toNat+1)+4 := by
  rw [body_shape]
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub]
    exact Nat.zero_le _
  · have actual:=Arenas.mark_call source .down "mark" 2701127680#64 afterMark (Arenas.Scratch.mark_code source.code arena.code) arena.scratch (by omega)
    change evaluateHOLFiniteState source (.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark)=_ at actual
    rw [actual]
    let marked:=bind {source with clock:=source.clock-1} "mark" 2701127680#64
    let ready:=bind marked "e" 0#64
    have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
      (bind_lookup_other marked "e" "p" 0#64 (by decide)).trans ((bind_lookup_other {source with clock:=source.clock-1} "mark" "p" 2701127680#64 (by decide)).trans pointerCell)
    have readyLength : ready.locals.lookup (ofString "len")=some (.val (.word length)) :=
      (bind_lookup_other marked "e" "len" 0#64 (by decide)).trans ((bind_lookup_other {source with clock:=source.clock-1} "mark" "len" 2701127680#64 (by decide)).trans lengthCell)
    have readyArena : CurrentStartup.ArenaState ready := arena.of_frame rfl
    have front:=caught_cost ready pointer length readyPointer readyLength readyArena fits
    have tail : ClockCost.Bound source.code (.seq release (.return (.const 0#64))) 1 :=
      ClockCost.sequence source.code _ _ 1 0 (Arenas.Scratch.release_call_price source.code arena.code _) (ClockCost.returned source.code _)
    have joined:=ClockCost.sequence_current ready caught (.seq release (.return (.const 0#64))) (14*(length.toNat+1)+2) 1 front tail
    have declared:=ClockCost.declared_current marked "e" (.const 0#64) 0#64 afterError (14*(length.toNat+1)+2+1) rfl joined
    have monotone:=evaluateHOLFiniteState_clock_le marked afterMark
    change source.clock-1-(evaluateHOLFiniteState marked afterMark).2.clock≤14*(length.toNat+1)+2+1 at declared
    change (evaluateHOLFiniteState marked afterMark).2.clock≤source.clock-1 at monotone
    change source.clock-(evaluateHOLFiniteState marked afterMark).2.clock≤_
    omega

end InitECandidate.Solver.Rlp.CurrentValidate

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.original_code
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.caught_cost
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_cost
