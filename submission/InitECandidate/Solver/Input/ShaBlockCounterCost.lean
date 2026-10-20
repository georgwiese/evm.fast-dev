import InitECandidate.Solver.Input.ShaFixedCost
import InitECandidate.Solver.Input.QuietClockEffects
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def blockBody : ProgHOL 64 := match Guest.guestFn_sha256_block with | .function fn=>progToHOL fn.body | _=>.skip
def blockSuffix : ProgHOL 64 := match blockBody with | .seq _ rest=>rest | _=>.skip
def firstLoop : ProgHOL 64 := (BuildProgram.loops blockBody)[0]?.getD .skip
def secondLoop : ProgHOL 64 := (BuildProgram.loops blockBody)[1]?.getD .skip
def firstStep : ProgHOL 64 := match firstLoop with | .while _ body=>body | _=>.skip
def secondStep : ProgHOL 64 := match secondLoop with | .while _ body=>body | _=>.skip
def accelerator : ProgHOL 64 := .extCall (ofString "sha256f") (.var .global (ofString "sha_accel")) (.const 0#64) (.var .global (ofString "sha_accel")) (.const 96#64)
def resetCounter : ProgHOL 64 := .assign .local (ofString "i") (.const 0#64)
def secondSuffix : ProgHOL 64 := .seq (.while (.cmp .less (localVar "i") (.const 4#64)) secondStep) (.return (.const 0#64))

set_option maxRecDepth 10000 in
theorem block_suffix_shape : blockSuffix=.dec (ofString "i") .one (.const 0#64)
    (.seq (.while (.cmp .less (localVar "i") (.const 4#64)) firstStep) (.seq accelerator (.seq resetCounter secondSuffix))) := by
  simp only [blockSuffix,blockBody,firstStep,firstLoop,secondStep,secondLoop,BuildProgram.loops,Guest.guestFn_sha256_block,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,accelerator,resetCounter,secondSuffix,localVar]

set_option maxRecDepth 10000 in
private theorem steps_quiet (code) : QuietClock.Preserves code firstStep ∧ QuietClock.Preserves code secondStep := by
  constructor
  all_goals simp only [firstStep,firstLoop,secondStep,secondLoop,blockBody,BuildProgram.loops,Guest.guestFn_sha256_block,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  all_goals repeat' first | apply QuietClock.declared | apply QuietClock.sequence | exact QuietClock.store code _ _ | exact QuietClock.assign code _ _

set_option maxRecDepth 10000 in
private theorem steps_advance : CounterFlow.Advances (ofString "i") 1 firstStep ∧ CounterFlow.Advances (ofString "i") 1 secondStep := by
  constructor
  all_goals simp only [firstStep,firstLoop,secondStep,secondLoop,blockBody,BuildProgram.loops,Guest.guestFn_sha256_block,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  · apply CounterFlow.declared (other:=by decide)
    apply CounterFlow.declared (other:=by decide)
    exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.store _ _)) (CounterFlow.increment _)
  · apply CounterFlow.declared (other:=by decide)
    apply CounterFlow.sequence (left:=0) (right:=1)
    · exact CounterFlow.preserved _ _ (.store _ _)
    · exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.store _ _)) (CounterFlow.increment _)

set_option maxRecDepth 10000 in
private theorem steps_safe : LocalPrefix (ofString "marker") firstStep ∧ LocalPrefix (ofString "marker") secondStep := by
  constructor
  all_goals simp only [firstStep,firstLoop,secondStep,secondLoop,blockBody,BuildProgram.loops,Guest.guestFn_sha256_block,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  all_goals
    repeat' first
    | apply LocalPrefix.dec (other:=by decide)
    | apply LocalPrefix.seq
    | exact LocalPrefix.store _ _
    | exact LocalPrefix.assign _ _ (by decide)

/-- Both original SHA block counter loops together spend at most eight
source ticks, including arbitrary accelerator/memory failure outcomes. The
preceding optional64-byte copy is deliberately priced by its caller. -/
theorem block_suffix_price (code) : ClockCost.Bound code blockSuffix 8 := by
  have step1 := ClockCost.of_quiet code firstStep (steps_quiet code).1
  have step2 := ClockCost.of_quiet code secondStep (steps_quiet code).2
  have resetPrice : ClockCost.Bound code (.seq resetCounter secondSuffix) 4 := by
    intro source codeEq
    apply ClockCost.sequence_reached_current source resetCounter secondSuffix 0 4 (ClockCost.assign code _ _ source codeEq)
    intro middle normal
    have middleEq := assign_none source middle "i" (.const 0#64) 0#64 rfl normal
    have cell : middle.locals.lookup (ofString "i")=some (.val (.word 0#64)) := by rw [middleEq]; exact bind_lookup_same _ _ _
    have codeMiddle : middle.code=code := by rw [middleEq]; exact codeEq
    have cost := CounterFlow.constant_loop_cost code (ofString "i") (ofString "marker") secondStep 0 4 (by decide) step2 steps_advance.2 steps_safe.2 middle 0#64 codeMiddle cell (by decide)
    exact ClockCost.sequence_current middle _ _ 4 0 (by simpa [localVar] using cost) (ClockCost.returned middle.code _)
  have backPrice : ClockCost.Bound code (.seq accelerator (.seq resetCounter secondSuffix)) 4 :=
    ClockCost.sequence code _ _ 0 4 (ClockCost.of_quiet code _ (QuietClock.external code _ _ _ _ _)) resetPrice
  intro source codeEq
  rw [block_suffix_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 8 rfl
  let entry := bind source "i" 0#64
  have cost := CounterFlow.constant_loop_cost code (ofString "i") (ofString "marker") firstStep 0 4 (by decide) step1 steps_advance.1 steps_safe.1 entry 0#64 codeEq (bind_lookup_same _ _ _) (by decide)
  have entryCode : entry.code=code := codeEq
  exact ClockCost.sequence_current entry _ _ 4 4 (by simpa [localVar] using cost) (by rw [entryCode]; exact backPrice)

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_suffix_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_suffix_price
