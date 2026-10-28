import InitECandidate.Solver.MutableTable.MemeqAnyCost
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Environment
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 13 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_memeq) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Memeq32.body,Memeq32.formals,
    Guest.guestFn_memeq,Guest.Software.guestFn_memeq,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Any actual operand expressions, including failed or wrongly shaped
reads, are covered. A valid original call has the literal32 length and a
callee allowance independent of memory mapping; the quiet caller adds1. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ExpHOL 64)
    (name : MlS) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (quiet : Input.ClockCost.Bound source.code continuation 0) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "memeq") [first,second,.const 32#64] continuation)).2.clock≤129 := by
  classical
  cases firstRead : eval source first with
  | none=>
    simp only [eval] at firstRead
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp [evalListHOLFinite,evalListHOLExact,firstRead]
  | some left=>
    cases secondRead : eval source second with
    | none=>
      simp only [eval] at firstRead secondRead
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead]
    | some right=>
      let actualValues : List (ValueHOL 64):=[left,right,.val (.word 32#64)]
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,second,.const 32#64]=some actualValues := by
        simp only [eval] at firstRead secondRead
        simp [actualValues,evalListHOLFinite,evalListHOLExact,firstRead,secondRead,evalHOLExact]
      cases left <;> cases right
      case val.val a b=>
        cases a with
        | word a=>
          cases b with
          | word b=>
            obtain ⟨callee,called,aCell,bCell,nCell⟩ := MemeqByteRuntime.environment source.code.lookup a b 32 code
            exact Input.ClockCost.scoped_current source name .one (ofString "memeq") [first,second,.const 32#64] _ Memeq32.body continuation callee .one 128 0 args called
              (body_cost (callEntryStateHOLFinite source callee) nCell) quiet
      all_goals
        have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") actualValues=none := by
          apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup (ofString "memeq") actualValues).mpr
          unfold lookupCodeHOLExact
          rw [code]
          simp [actualValues,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite,args]
        simp [failed]

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.original_code
#print axioms InitECandidate.Solver.MutableTable.MemeqAny.scoped_cost
