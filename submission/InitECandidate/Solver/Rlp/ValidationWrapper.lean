import InitECandidate.Solver.Rlp.ValidationCost
import InitECandidate.Solver.Rlp.Environment
import InitECandidate.Solver.Arenas.ScratchScope
import InitECandidate.Solver.Input.ClockCostCaught

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_validate_items with | .function fn=>progToHOL fn.body | _=>.skip
def release : ProgHOL 64 := .call (some (none,none)) (ofString "scratch_release") [localVar "mark"]
def handler : ProgHOL 64 := .seq release (.raise (ofString "RlpErr") (localVar "e"))
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def caught : ProgHOL 64 := .call (some (none,some (ofString "RlpErr",ofString "e",handler))) (ofString "_rlp_validate_items_body") arguments
def afterError : ProgHOL 64 := .seq caught (.seq release (.return (.const 0#64)))
def afterMark : ProgHOL 64 := .dec (ofString "e") .one (.const 0#64) afterError

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark := by
  simp only [body,afterMark,afterError,caught,handler,release,arguments,localVar,Guest.guestFn_rlp_validate_items,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_validate_items")=some (Header.formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 99 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_validate_items) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,
    Guest.guestFn_rlp_validate_items,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem handler_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code handler 1 :=
  Input.ClockCost.sequence code _ _ 1 0 (Arenas.Scratch.release_call_price code installed _)
    (Input.ClockCost.of_quiet code _ (Input.QuietClock.raised code _ _))

theorem caught_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source caught).2.clock≤14*(2*length.toNat+1)+2 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "_rlp_validate_items_body") Validation.body .one pointer length (Validation.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  have currentArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  exact Input.ClockCost.caught_current source (ofString "_rlp_validate_items_body") arguments _ Validation.body callee .one (ofString "RlpErr") (ofString "e") handler (14*(2*length.toNat+1)) 1 args called
    (Validation.body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal currentArena fits installed) (handler_price source.code installed)

/-- Full original public validator wrapper, including mark/release and
caught RLP errors. The bound covers all outcomes without funding or any
assumed future helper result. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤14*(2*length.toNat+1)+4 := by
  rw [body_shape]
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub]
    exact Nat.zero_le _
  · have actual := Arenas.mark_call source .down "mark" cursor afterMark (Arenas.Scratch.mark_code source.code installed) arena.cursorGlobal (by omega)
    change evaluateHOLFiniteState source (.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark)=_ at actual
    rw [actual]
    let marked := bind {source with clock:=source.clock-1} "mark" cursor
    let ready := bind marked "e" 0#64
    have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
      (bind_lookup_other _ "e" "p" _ (by decide)).trans ((bind_lookup_other _ "mark" "p" _ (by decide)).trans pointerCell)
    have readyLength : ready.locals.lookup (ofString "len")=some (.val (.word length)) :=
      (bind_lookup_other _ "e" "len" _ (by decide)).trans ((bind_lookup_other _ "mark" "len" _ (by decide)).trans lengthCell)
    have readyArena := Validation.Arena.of_fields source ready cursor limit arena rfl rfl
    have front := caught_cost ready pointer length cursor limit readyPointer readyLength readyArena fits installed
    have tail : Input.ClockCost.Bound source.code (.seq release (.return (.const 0#64))) 1 :=
      Input.ClockCost.sequence source.code _ _ 1 0 (Arenas.Scratch.release_call_price source.code installed _) (Input.ClockCost.returned source.code _)
    have joined := Input.ClockCost.sequence_current ready caught (.seq release (.return (.const 0#64))) (14*(2*length.toNat+1)+2) 1 front tail
    have declared := Input.ClockCost.declared_current marked "e" (.const 0#64) 0#64 afterError (14*(2*length.toNat+1)+2+1) rfl joined
    have monotone := evaluateHOLFiniteState_clock_le marked afterMark
    change source.clock-1-(evaluateHOLFiniteState marked afterMark).2.clock≤14*(2*length.toNat+1)+2+1 at declared
    change (evaluateHOLFiniteState marked afterMark).2.clock≤source.clock-1 at monotone
    change source.clock-(evaluateHOLFiniteState marked afterMark).2.clock≤_
    omega

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.body_shape
#print axioms InitECandidate.Solver.Rlp.Validate.original_code
#print axioms InitECandidate.Solver.Rlp.Validate.handler_price
#print axioms InitECandidate.Solver.Rlp.Validate.caught_cost
#print axioms InitECandidate.Solver.Rlp.Validate.body_cost
