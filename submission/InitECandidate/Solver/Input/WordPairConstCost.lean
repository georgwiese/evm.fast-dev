import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Price a genuine two-word scoped call with a constant second operand.
Failed reads and failed ABI checks are included in the same allowance. -/
theorem word_pair_const (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function leftName rightName name : MlS) (body continuation : ProgHOL 64)
    (shape returnShape : ShapeHOL) (first : ExpHOL 64) (right : BitVec 64) (price tailPrice : Nat)
    (different : leftName≠rightName)
    (code : source.code.lookup function=some ([(leftName,.one),(rightName,.one)],body,returnShape))
    (priced : ∀ (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (left : BitVec 64),
      entry.code=source.code → entry.locals.lookup leftName=some (.val (.word left)) → entry.locals.lookup rightName=some (.val (.word right)) →
      entry.clock-(evaluateHOLFiniteState entry body).2.clock≤price)
    (tail : Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name shape function [first,.const right] continuation)).2.clock≤price+tailPrice+1 := by
  classical
  cases firstRead : eval source first with
  | none=>
    simp only [eval] at firstRead
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    simp [evalListHOLFinite,evalListHOLExact,firstRead]
  | some left=>
    let actualValues : List (ValueHOL 64):=[left,.val (.word right)]
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [first,.const right]=some actualValues := by
      simp only [eval] at firstRead
      simp [actualValues,evalListHOLFinite,evalListHOLExact,firstRead,evalHOLExact]
    cases left with
    | val payload=>
      cases payload with
      | word left=>
        obtain ⟨callee,called,aCell,bCell⟩:=word_pair_environment source.code.lookup function leftName rightName body returnShape left right different code
        exact scoped_current source name shape function [first,.const right] _ body continuation callee returnShape price tailPrice args called
          (priced (callEntryStateHOLFinite source callee) left rfl aCell bCell) tail
    | rStruct fields | nStruct constructor fields=>
      have failed : lookupCodeHOLFinite source.code.lookup function actualValues=none := by
        apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup function actualValues).mpr
        unfold lookupCodeHOLExact
        rw [code]
        simp [actualValues,shapeOfHOLExact,shapeEqHOL]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite,args]
      simp [failed]

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.word_pair_const
