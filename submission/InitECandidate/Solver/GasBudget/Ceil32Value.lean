import InitECandidate.Solver.GasBudget.ChargeWithMemoryProgram
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.GasBudget.Ceil32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body := MemoryCostEffects.Kind.ceil32.body
def remainder (v : BitVec 64) := v &&& 31#64
def resultWord (v : BitVec 64) := if remainder v = 0#64 then v else SaturatingAdd.resultWord v (32#64 - remainder v)
def price (v : BitVec 64) : Nat := if remainder v = 0#64 then 0 else 1
def guard : ProgHOL 64 := .ite (.cmp .equal (localVar "r") (.const 0#64)) (.return (localVar "v")) .skip
def afterGuard : ProgHOL 64 := .decCall (ofString "s") .one (ofString "add_sat")
  [localVar "v", .op .sub [.const 32#64, localVar "r"]] (.return (localVar "s"))
def afterR : ProgHOL 64 := .seq guard afterGuard

theorem body_shape : body = .dec (ofString "r") .one (.op .and [localVar "v", .const 31#64]) afterR := by
  simp only [body, MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature, MemoryCostEffects.Kind.original,
    Guest.guestFn_ceil32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    afterR, guard, afterGuard, localVar]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (v : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (vLocal : source.locals.lookup (ofString "v") = some (.val (.word v))) (enough : price v ≤ source.clock) :
    ∃ target, evaluateHOLFiniteState source body = (some (.returned (.val (.word (resultWord v)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - price v} := by
  classical
  let entered := WitnessRadix.QueryBranch.bind source "r" (remainder v)
  have vE : entered.locals.lookup (ofString "v") = some (.val (.word v)) :=
    (bind_lookup_other _ "r" "v" _ (by decide)).trans vLocal
  have rE : entered.locals.lookup (ofString "r") = some (.val (.word (remainder v))) := bind_lookup_same _ _ _
  have read : eval source (.op .and [localVar "v", .const 31#64]) = some (.val (.word (remainder v))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, vLocal, valueIsWord, valueWord, wordOpHOL, wordOp, remainder]
    rfl
  have inner : ∃ target, evaluateHOLFiniteState entered afterR = (some (.returned (.val (.word (resultWord v)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - price v} := by
    by_cases zero : remainder v = 0#64
    · refine ⟨emptyLocalsHOLFinite entered, ?_, ?_⟩
      · simp [afterR, guard, evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
          evalHOLExact, toExact, localVar, vE, rE, zero, resultWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
          shapeOfHOLExact, sizeOfShapeWithContextHOL, fixClockHOLFinite, emptyLocalsHOLFinite]
      · simp [price, zero, entered, WitnessRadix.QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite]
    · have guardRun : evaluateHOLFiniteState entered guard = (none, entered) := by
        simp [guard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar, rE,
          zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
          [localVar "v", .op .sub [.const 32#64, localVar "r"]] = some [.val (.word v), .val (.word (32#64 - remainder v))] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, vE, rE, valueIsWord, valueWord, wordOpHOL, wordOp]
      have code := OriginalCodeEnvironment.arithmetic entered.code installed .add_sat
      rw [ChargeWithMemory.add_signature] at code
      let ready := WitnessRadix.QueryBranch.bind {entered with clock := entered.clock - 1} "s" (SaturatingAdd.resultWord v (32#64 - remainder v))
      have sLocal : ready.locals.lookup (ofString "s") = some (.val (.word (SaturatingAdd.resultWord v (32#64 - remainder v)))) := bind_lookup_same _ _ _
      have returnRun : evaluateHOLFiniteState ready (.return (localVar "s")) =
          (some (.returned (.val (.word (SaturatingAdd.resultWord v (32#64 - remainder v))))), emptyLocalsHOLFinite ready) := by
        simp [evaluateHOLFiniteState_return, evalHOLExact, toExact, localVar, sLocal, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      refine ⟨restore entered "s" (emptyLocalsHOLFinite ready), ?_, ?_⟩
      · rw [afterR, WitnessRadix.StateSteps.next_sequence _ _ _ _ guardRun (Nat.le_refl _), afterGuard,
          SaturatingAdd.call_execute entered v (32#64 - remainder v) "s" _ _ args code (by change 1 ≤ source.clock; simpa [price, zero] using enough), returnRun]
        simp only [resultWord, if_neg zero]
      · simp only [emptyLocalsHOLFinite, restore, ready, entered, WitnessRadix.QueryBranch.bind, setVarHOLFinite, price, if_neg zero]
  obtain ⟨target, run, frame⟩ := inner
  refine ⟨restore source "r" target, ?_, frame⟩
  rw [body_shape]
  exact Input.ScalarScope.declare_execute source target "r" _ (remainder v) afterR _ read run

theorem ge_self (v : BitVec 64) : v ≤ resultWord v := by
  unfold resultWord
  split
  · change v.toNat ≤ v.toNat
    omega
  · exact SaturatingAdd.ge_left _ _

theorem zero : resultWord 0#64 = 0#64 := by decide

end InitECandidate.Solver.GasBudget.Ceil32

#print axioms InitECandidate.Solver.GasBudget.Ceil32.execute
#print axioms InitECandidate.Solver.GasBudget.Ceil32.ge_self
#print axioms InitECandidate.Solver.GasBudget.Ceil32.zero
