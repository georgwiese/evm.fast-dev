import InitECandidate.Solver.GasBudget.WordsOfRange
import InitECandidate.Solver.GasBudget.Ceil32Value

namespace InitECandidate.Solver.GasBudget.WordsOf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def resultWord (n : BitVec 64) : BitVec 64 := Ceil32.resultWord n >>> (5 : Nat)
def price (n : BitVec 64) : Nat := 1 + Ceil32.price n

theorem ceil_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "ceil32") = some ([(ofString "v", .one)], Ceil32.body, .one) := by
  simpa only [Ceil32.body, MemoryCostEffects.Kind.name, MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature,
    MemoryCostEffects.Kind.original, Guest.guestFn_ceil32, shapeToHOL, List.map_cons, List.map_nil, paramToHOL]
    using MemoryCostEffects.entry code installed .ceil32

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (n : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (nLocal : source.locals.lookup (ofString "n") = some (.val (.word n))) (enough : price n ≤ source.clock) :
    ∃ target, evaluateHOLFiniteState source body = (some (.returned (.val (.word (resultWord n)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - price n} := by
  classical
  obtain ⟨callee, called, binding⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "ceil32") "v" Ceil32.body n (ceil_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target, run, frame⟩ := Ceil32.execute entry n installed binding (by change Ceil32.price n ≤ source.clock - 1; unfold price at enough; omega)
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "n"] = some [.val (.word n)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, nLocal]
  have callRun := Input.CallNormal.pure_return_execute source target "c" (ofString "ceil32") [localVar "n"] [.val (.word n)] Ceil32.body
    (.return shifted) callee (Ceil32.resultWord n) (Ceil32.price n) args called (by unfold price at enough; omega) run frame
  let ready := WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1 - Ceil32.price n} "c" (Ceil32.resultWord n)
  have bindingC : ready.locals.lookup (ofString "c") = some (.val (.word (Ceil32.resultWord n))) := bind_lookup_same _ _ _
  have finish : evaluateHOLFiniteState ready (.return shifted) = (some (.returned (.val (.word (resultWord n)))), emptyLocalsHOLFinite ready) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, toExact, shifted, localVar, bindingC, wordShiftHOL, resultWord,
      shapeOfHOLExact, sizeOfShapeWithContextHOL]
  refine ⟨restore source "c" (emptyLocalsHOLFinite ready), ?_, ?_⟩
  · rw [body_shape, callRun, finish]
  · have clock : source.clock - 1 - Ceil32.price n = source.clock - price n := by unfold price; omega
    change emptyLocalsHOLFinite {source with clock := source.clock - 1 - Ceil32.price n} = _
    rw [clock]

/-- The true original word count dominates the floor of the byte count.
This is the linear part of the later memory/copy accounting. -/
theorem lower (n : BitVec 64) : n.toNat / 32 ≤ (resultWord n).toNat := by
  have rounded : n.toNat ≤ (Ceil32.resultWord n).toNat := Ceil32.ge_self n
  simp only [resultWord, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change n.toNat / 32 ≤ (Ceil32.resultWord n).toNat / 32
  omega

theorem upper (n : BitVec 64) : (resultWord n).toNat ≤ 576460752303423487 := by
  have bound := (Ceil32.resultWord n).isLt
  simp only [resultWord, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem zero : resultWord 0#64 = 0#64 := by simp [resultWord, Ceil32.zero]

end InitECandidate.Solver.GasBudget.WordsOf

#print axioms InitECandidate.Solver.GasBudget.WordsOf.execute
#print axioms InitECandidate.Solver.GasBudget.WordsOf.lower
#print axioms InitECandidate.Solver.GasBudget.WordsOf.upper
#print axioms InitECandidate.Solver.GasBudget.WordsOf.zero
