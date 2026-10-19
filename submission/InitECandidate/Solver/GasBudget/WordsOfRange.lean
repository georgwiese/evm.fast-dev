import InitECandidate.Solver.GasBudget.MemoryCostNoException
import InitECandidate.Solver.Input.RlpWrite.U256Shape
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.WordsOf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body := MemoryCostEffects.Kind.words_of.body
def formals : List (MlS × ShapeHOL) := [(ofString "n", .one)]
def shifted : ExpHOL 64 := .shift .lsr (localVar "c") (.const 5#64)

theorem body_shape : body = .decCall (ofString "c") .one (ofString "ceil32") [localVar "n"] (.return shifted) := by
  simp only [body, MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature, MemoryCostEffects.Kind.original,
    Guest.guestFn_words_of, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, shifted, localVar]

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "words_of") = some (formals, body, .one) := by
  simpa only [formals, body, MemoryCostEffects.Kind.name, MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature,
    MemoryCostEffects.Kind.original, Guest.guestFn_words_of, declToHOL, funDeclToHOL, shapeToHOL, List.map_cons, List.map_nil,
    paramToHOL] using MemoryCostEffects.entry code installed .words_of

/-- Actual successful words_of always returns a scalar of at most2^59-1.
The final unsigned shift suffices; no assumed input bound or ceil32 result. -/
theorem body_range (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), target)) :
    ∃ word : BitVec 64, returned = .val (.word word) ∧ word.toNat ≤ 576460752303423487 := by
  rw [body_shape] at normal
  obtain ⟨positive, values, actual, callee, shape, post, rounded, inner, args, called, run, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source target "c" .one (ofString "ceil32") [localVar "n"] (.return shifted) returned normal
  have scalar : shapeOfHOLExact rounded = .one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨value, roundedEq⟩ := Input.RlpWrite.U256Value.scalar_word rounded scalar
  let entry := Input.CallNormal.continuationEntry source post "c" rounded
  have binding : entry.locals.lookup (ofString "c") = some (.val (.word value)) := by
    simp [entry, Input.CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, roundedEq]
  obtain ⟨read, exactState⟩ := Input.return_normal entry inner shifted returned tailRun
  have evaluated : eval entry shifted = some (.val (.word (value >>> (5 : Nat)))) := by
    simp [eval, shifted, localVar, evalHOLExact, toExact, binding, wordShiftHOL]
  have returnedEq : returned = .val (.word (value >>> (5 : Nat))) := Option.some.inj (read.symm.trans evaluated)
  refine ⟨value >>> (5 : Nat), returnedEq, ?_⟩
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have bound := value.isLt
  omega

/-- The actual copy/hash fee expression cannot wrap for the returned range.
Both original slopes3and6 fit comfortably in a64bit word. -/
theorem fee_numbers (word : BitVec 64) (small : word.toNat ≤ 576460752303423487)
    (base slope : Nat) (baseBound : base ≤ 3000) (slopeBound : slope ≤ 6) :
    (BitVec.ofNat 64 base + BitVec.ofNat 64 slope * word).toNat = base + slope * word.toNat ∧
      base ≤ (BitVec.ofNat 64 base + BitVec.ofNat 64 slope * word).toNat := by
  have productBound : slope * word.toNat ≤ 6 * 576460752303423487 := Nat.mul_le_mul slopeBound small
  have slopeFits : slope < 2 ^ 64 := by omega
  have baseFits : base < 2 ^ 64 := by omega
  have product : (BitVec.ofNat 64 slope * word).toNat = slope * word.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt slopeFits, Nat.mod_eq_of_lt (by omega)]
  have first : (BitVec.ofNat 64 base).toNat = base := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseFits]
  have fits : (BitVec.ofNat 64 base).toNat + (BitVec.ofNat 64 slope * word).toNat < 2 ^ 64 := by rw [first, product]; omega
  rw [BitVec.toNat_add_of_lt fits, first, product]
  exact ⟨rfl, Nat.le_add_right _ _⟩

end InitECandidate.Solver.GasBudget.WordsOf

#print axioms InitECandidate.Solver.GasBudget.WordsOf.body_range
#print axioms InitECandidate.Solver.GasBudget.WordsOf.fee_numbers
