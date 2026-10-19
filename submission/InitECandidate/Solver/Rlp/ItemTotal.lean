import InitECandidate.Solver.Rlp.ValidationCall
import InitECandidate.Solver.Rlp.HeaderValidCost

namespace InitECandidate.Solver.Rlp.ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_rlp_item_total with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64) := [localVar "p",localVar "len"]
def payloadArguments : List (ExpHOL 64) := [.op .add [localVar "p",.rfield 0 (localVar "h")],.rfield 1 (localVar "h")]
def validate : ProgHOL 64 := .call (some (none,none)) (ofString "rlp_validate_items") payloadArguments
def check : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 2 (localVar "h")) (.const 0#64)) validate .skip
def total : ExpHOL 64 := .op .add [.rfield 0 (localVar "h"),.rfield 1 (localVar "h")]
def afterHeader : ProgHOL 64 := .seq check (.return total)

theorem body_shape : body=.decCall (ofString "h") Header.resultShape (ofString "rlp_item_header") arguments afterHeader := by
  simp only [body,arguments,afterHeader,check,validate,payloadArguments,total,Header.resultShape,localVar,
    Guest.guestFn_rlp_item_total,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "rlp_item_total")=some (Header.formals,body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 100 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_rlp_item_total) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Header.formals,
    Guest.guestFn_rlp_item_total,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem payload_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag)) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) payloadArguments=some (Header.values (pointer+header) payload) := by
  simp [payloadArguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,headerCell,
    Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem check_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header payload flag : BitVec 64)
    (cell : source.locals.lookup (ofString "h")=some (Header.result header payload flag)) :
    evaluateHOLFiniteState source check=if flag≠0#64 then evaluateHOLFiniteState source validate else evaluateHOLFiniteState source .skip := by
  simp [check,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,cell,Header.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The actual decoded payload controls this local allowance. This form is
retained for later amortization by actual item size across a list. -/
theorem after_header_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+header.toNat+payload.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterHeader).2.clock≤14*(2*payload.toNat+1)+5 := by
  have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  have front : source.clock-(evaluateHOLFiniteState source check).2.clock≤14*(2*payload.toNat+1)+5 := by
    rw [check_evaluate source header payload flag headerCell]
    by_cases zero : flag=0#64
    · rw [if_neg (not_not_intro zero),evaluateHOLFiniteState_skip]
      change source.clock-source.clock≤_
      omega
    · rw [if_pos zero]
      exact Validate.call_cost source (pointer+header) payload cursor limit (some none) payloadArguments
        (payload_arguments source pointer header payload flag pointerCell headerCell) arena (by rw [number]; exact fits) installed
  exact Input.ClockCost.sequence_current source check (.return total) (14*(2*payload.toNat+1)+5) 0 front (Input.ClockCost.returned source.code total)

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤28*length.toNat+30 := by
  rw [body_shape]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  have actual := Header.scoped_valid_cost source pointer length "h" arguments afterHeader (14*(2*length.toNat+1)+5) args installed ?_
  · omega
  · intro paid answer valid
    obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩ := valid
    rw [same]
    let ready := setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
    have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
      simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "h"≠ofString "p" from by decide] using pointerCell
    have readyHeader : ready.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
      simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have priced := after_header_cost ready pointer header payload flag cursor limit readyPointer readyHeader
      (Validation.Arena.of_fields source ready cursor limit arena rfl rfl) (by omega) installed
    change source.clock-paid-(evaluateHOLFiniteState ready afterHeader).2.clock≤_ at priced ⊢
    omega

end InitECandidate.Solver.Rlp.ItemTotal

#print axioms InitECandidate.Solver.Rlp.ItemTotal.body_shape
#print axioms InitECandidate.Solver.Rlp.ItemTotal.original_code
#print axioms InitECandidate.Solver.Rlp.ItemTotal.payload_arguments
#print axioms InitECandidate.Solver.Rlp.ItemTotal.check_evaluate
#print axioms InitECandidate.Solver.Rlp.ItemTotal.after_header_cost
#print axioms InitECandidate.Solver.Rlp.ItemTotal.body_cost
