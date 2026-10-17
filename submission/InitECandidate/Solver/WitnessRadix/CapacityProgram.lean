import InitECandidate.Solver.ConstructorSyntax
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.WitnessRadix.Capacity
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def condition : ExpHOL 64 := .cmp .lower (localVar "cap")
  (.op .add [.panop .mul [.const 2#64, localVar "n"], .const 2#64])
def step : ProgHOL 64 := .assign .local (ofString "cap") (.panop .mul [localVar "cap", .const 2#64])

theorem loop_shape : Constructor.capacityLoop = .while condition step := by
  rfl

theorem condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (count exponent : Nat)
    (small : count < 2 ^ 31) (powerBound : exponent ≤ 32)
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ exponent))))) :
    @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition =
      some (.val (.word (if 2 ^ exponent < 2 * count + 2 then 1#64 else 0#64))) := by
  have powerSmall : 2 ^ exponent < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have countSmall : count < 2 ^ 64 := by omega
  have thresholdSmall : 2 * count + 2 < 2 ^ 64 := by omega
  have threshold : 2#64 * BitVec.ofNat 64 count + 2#64 = BitVec.ofNat 64 (2 * count + 2) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_mul]
  simp [condition, localVar, evalHOLFinite, evalHOLExact, evalListHOLExact, toExact, countLocal, capLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    threshold, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt powerSmall, Nat.mod_eq_of_lt thresholdSmall]

theorem step_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (exponent : Nat)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ exponent))))) :
    evaluateHOLFiniteState source step = (none, bind source "cap" (BitVec.ofNat 64 (2 ^ (exponent + 1)))) := by
  apply StateSteps.assign_execute source "cap" _ _ _ capLocal
  simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, capLocal, valueIsWord, valueWord, panOpHOL,
    Nat.pow_succ, BitVec.ofNat_mul]

end InitECandidate.Solver.WitnessRadix.Capacity

#print axioms InitECandidate.Solver.WitnessRadix.Capacity.loop_shape
#print axioms InitECandidate.Solver.WitnessRadix.Capacity.condition_read
#print axioms InitECandidate.Solver.WitnessRadix.Capacity.step_execute
