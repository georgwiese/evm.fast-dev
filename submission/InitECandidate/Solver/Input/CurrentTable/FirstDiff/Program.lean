import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.PanState
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_first_diff with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "a",.one),(ofString "b",.one),(ofString "key_len",.one)]
def afterI : ProgHOL 64 := match body with | .dec _ _ _ rest => rest | _ => .skip
def loop : ProgHOL 64 := match afterI with | .seq first _ => first | _ => .skip
def step : ProgHOL 64 := match loop with | .while _ rest => rest | _ => .skip
def afterX : ProgHOL 64 := match step with | .dec _ _ _ rest => rest | _ => .skip
def choice : ProgHOL 64 := match afterX with | .seq first _ => first | _ => .skip
def different : ProgHOL 64 := match choice with | .ite _ yes _ => yes | _ => .skip
def bitLoop : ProgHOL 64 := match different with | .dec _ _ _ rest => rest | _ => .skip
def bitStep : ProgHOL 64 := match bitLoop with | .while _ rest => rest | _ => .skip
def bitGuard : ProgHOL 64 := match bitStep with | .seq first _ => first | _ => .skip
def bitTest : ExpHOL 64 := match bitGuard with | .ite test _ _ => test | _ => .const 0#64
def bitResult : ExpHOL 64 := .op .add [.panop .mul [localVar "i",.const 8#64],localVar "j"]
def increment (name : String) : ProgHOL 64 := .assign .local (ofString name) (.op .add [localVar name,.const 1#64])
def readX : ExpHOL 64 := .op .xor [.loadByte (.op .add [localVar "a",localVar "i"]),.loadByte (.op .add [localVar "b",localVar "i"])]
def test : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "key_len")
def bitLimit : ExpHOL 64 := .cmp .less (localVar "j") (.const 8#64)

set_option maxRecDepth 100000 in
theorem shapes :
    body = .dec (ofString "i") .one (.const 0#64) afterI ∧
    afterI = .seq loop (.return (.panop .mul [localVar "key_len",.const 8#64])) ∧
    loop = .while test step ∧
    step = .dec (ofString "x") .one readX afterX ∧
    afterX = .seq choice (increment "i") ∧
    choice = .ite (.cmp .notEqual (localVar "x") (.const 0#64)) different .skip ∧
    different = .dec (ofString "j") .one (.const 0#64) bitLoop ∧
    bitLoop = .while bitLimit bitStep ∧
    bitStep = .seq bitGuard (increment "j") ∧
    bitGuard = .ite bitTest (.return bitResult) .skip := by
  simp only [body,afterI,loop,step,afterX,choice,different,bitLoop,bitStep,bitGuard,bitTest,
    bitResult,increment,readX,test,bitLimit,Guest.Software.guestFn_htab_first_diff,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_first_diff") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 118
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_first_diff) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_first_diff,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem bit_flow (key : MlS) (other : key ≠ ofString "j") : LocalFlow key bitStep := by
  rw [shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2]
  exact .seq (.ite _ (.returned _) (.base .skip)) (.base (.assign _ _ other))

theorem choice_flow (key : MlS) (other : key ≠ ofString "j") : LocalFlow key choice := by
  rw [shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1]
  exact .ite _ (.dec _ _ _ other (.loop _ (bit_flow key other))) (.base .skip)

theorem step_flow (key : MlS) (notX : key ≠ ofString "x")
    (notI : key ≠ ofString "i") (notJ : key ≠ ofString "j") : LocalFlow key step := by
  rw [shapes.2.2.2.1,shapes.2.2.2.2.1]
  exact .dec _ _ _ notX (.seq (choice_flow key notJ) (.base (.assign _ _ notI)))

theorem bit_advance : CounterFlow.Advances (ofString "j") 1 bitStep := by
  rw [shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2]
  have guardFlow : LocalFlow (ofString "j") (.ite bitTest (.return bitResult) .skip) :=
    .ite _ (.returned _) (.base .skip)
  exact CounterFlow.sequence _ _ _ 0 1 (CounterFlow.flow_preserved _ _ guardFlow) (CounterFlow.increment _)

theorem step_advance : CounterFlow.Advances (ofString "i") 1 step := by
  rw [shapes.2.2.2.1,shapes.2.2.2.2.1]
  exact CounterFlow.declared _ _ _ _ _ _ (by decide)
    (CounterFlow.sequence _ _ _ 0 1 (CounterFlow.flow_preserved _ _ (choice_flow _ (by decide))) (CounterFlow.increment _))

theorem bit_quiet (code) : QuietClock.Preserves code bitStep := by
  rw [shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2]
  exact QuietClock.sequence code _ _
    (QuietClock.conditional code _ _ _ (QuietClock.returned code _) (QuietClock.skip code))
    (QuietClock.assign code _ _)

theorem readonly (code) : LocalEffects.Preserves code body := by
  rw [shapes.1,shapes.2.1,shapes.2.2.1,shapes.2.2.2.1,shapes.2.2.2.2.1,
    shapes.2.2.2.2.2.1,shapes.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.1,
    shapes.2.2.2.2.2.2.2.2.1,shapes.2.2.2.2.2.2.2.2.2]
  exact LocalEffects.declared code _ _ _ _ (LocalEffects.sequence code _ _
    (LocalEffects.loop code _ _ (LocalEffects.declared code _ _ _ _ (LocalEffects.sequence code _ _
      (LocalEffects.conditional code _ _ _
        (LocalEffects.declared code _ _ _ _ (LocalEffects.loop code _ _ (LocalEffects.sequence code _ _
          (LocalEffects.conditional code _ _ _ (LocalEffects.returned code _) (LocalEffects.skip code))
          (LocalEffects.assign code _ _))))
        (LocalEffects.skip code))
      (LocalEffects.assign code _ _))))
    (LocalEffects.returned code _))

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.original_code
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.bit_advance
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.step_advance
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.readonly
