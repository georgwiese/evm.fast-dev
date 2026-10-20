import InitECandidate.Solver.Input.ConstantCounterCost
import InitECandidate.Solver.PanTraversal
import InitECandidate.Solver.Input.CounterDeclaration
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.GasBudget.MemoryWriterPrice

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def finishBody : ProgHOL 64 := match Guest.guestFn_sha256_finish with | .function fn=>progToHOL fn.body | _=>.skip
def finishLoop : ProgHOL 64 := (BuildProgram.loops finishBody)[0]?.getD .skip
def finishStep : ProgHOL 64 := match finishLoop with | .while _ body=>body | _=>.skip
def finishArguments : List (ExpHOL 64) := match finishStep with | .seq (.call _ _ args) _=>args | _=>[]
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])

theorem step_shape : finishStep=.seq (.call (some (none,none)) (ofString "st_be32") finishArguments) increment := by
  simp only [finishStep,finishLoop,finishBody,BuildProgram.loops,Guest.guestFn_sha256_finish,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some,Option.map_none,finishArguments,increment,localVar]

theorem finish_shape : finishBody=.dec (ofString "i") .one (.const 0#64)
    (.seq (.while (.cmp .less (localVar "i") (.const 8#64)) finishStep) (.return (.const 0#64))) := by
  simp only [finishStep,finishLoop,finishBody,BuildProgram.loops,Guest.guestFn_sha256_finish,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,Option.getD_some,localVar]

theorem finish_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code finishBody 16 := by
  have callPrice : ClockCost.Bound code (.call (some (none,none)) (ofString "st_be32") finishArguments) 1 :=
    GasBudget.MemoryWriter.call_price .be32 code installed (some none) finishArguments 0 (GasBudget.MemoryWriter.be32_price code)
  have stepPrice : ClockCost.Bound code finishStep 1 := by
    rw [step_shape]
    exact ClockCost.sequence code _ _ 1 0 callPrice (ClockCost.assign code _ _)
  have advance : CounterFlow.Advances (ofString "i") 1 finishStep := by
    rw [step_shape]
    exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.preserved _ _ (.call none _ _ (by intros; contradiction))) (CounterFlow.increment _)
  have safe : LocalPrefix (ofString "marker") finishStep := by
    rw [step_shape]
    exact .seq (.call none _ _ (by intros; contradiction)) (.assign _ _ (by decide))
  intro source codeEq
  rw [finish_shape]
  apply ClockCost.declared_current source "i" (.const 0#64) 0#64 _ 16 rfl
  let entry := bind source "i" 0#64
  have loopCost := CounterFlow.constant_loop_cost code (ofString "i") (ofString "marker") finishStep 1 8 (by decide) stepPrice advance safe entry 0#64 codeEq (bind_lookup_same _ _ _) (by decide)
  have priced := ClockCost.sequence_current entry (.while (.cmp .less (localVar "i") (.const 8#64)) finishStep) (.return (.const 0#64)) 16 0 (by simpa [localVar] using loopCost) (ClockCost.returned entry.code _)
  exact priced

def initializeBody : ProgHOL 64 := match Guest.guestFn_sha256_state_init with | .function fn=>progToHOL fn.body | _=>.skip

theorem initialize_price (code) : ClockCost.Bound code initializeBody 0 := by
  apply ClockCost.of_quiet
  simp only [initializeBody,Guest.guestFn_sha256_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat' first | apply QuietClock.sequence | exact QuietClock.store code _ _ | exact QuietClock.returned code _

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.step_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_shape
#print axioms InitECandidate.Solver.Input.ShaFixedCost.finish_price
#print axioms InitECandidate.Solver.Input.ShaFixedCost.initialize_price
