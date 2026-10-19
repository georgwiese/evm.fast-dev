import InitECandidate.Solver.GasBudget.MemoryCostValueResume
import InitECandidate.Solver.GasBudget.SaturatingAddPrefix
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.MemoryGasCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body := MemoryCostEffects.Kind.memory_gas_cost.body
def resultWord (size : BitVec 64) : BitVec 64 :=
  let w := WordsOf.resultWord size
  let sq := Mul64.parts w w
  if sq.2 ≠ 0#64 then 18446744073709551615#64 else SaturatingAdd.resultWord (w * 3#64) (sq.1 >>> (9 : Nat))
def guard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 1 (localVar "sq")) (.const 0#64)) (.return (.const 18446744073709551615#64)) .skip
def afterGuard : ProgHOL 64 := .decCall (ofString "a") .one (ofString "add_sat")
  [.panop .mul [localVar "w", .const 3#64], .shift .lsr (.rfield 0 (localVar "sq")) (.const 9#64)] (.return (localVar "a"))
def afterSquare : ProgHOL 64 := .seq guard afterGuard
def afterWords : ProgHOL 64 := .decCall (ofString "sq") (.comb [.one, .one]) (ofString "mul64x64") [localVar "w", localVar "w"] afterSquare

theorem body_shape : body = .decCall (ofString "w") .one (ofString "words_of") [localVar "size"] afterWords := by
  simp only [body, MemoryCostEffects.Kind.body, MemoryCostEffects.Kind.signature, MemoryCostEffects.Kind.original,
    Guest.guestFn_memory_gas_cost, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    afterWords, afterSquare, guard, afterGuard, localVar]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (size : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (sizeLocal : source.locals.lookup (ofString "size") = some (.val (.word size))) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word (resultWord size)) := by
  rw [body_shape] at normal
  obtain ⟨positive, values, actual, callee, shape, wTarget, wValue, wPost, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post "w" .one (ofString "words_of") [localVar "size"] afterWords returned normal
  have expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "size"] = some [.val (.word size)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, sizeLocal]
  have valuesEq := Option.some.inj (args.symm.trans expectedArgs)
  rw [valuesEq] at called
  obtain ⟨wEq, funded, next⟩ := WordsOf.resume_value source wTarget "w" size installed actual callee shape called wValue bodyRun
  rw [next] at tailRun
  let w := WordsOf.resultWord size
  let first := WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1 - WordsOf.price size} "w" w
  have firstW : first.locals.lookup (ofString "w") = some (.val (.word w)) := bind_lookup_same _ _ _
  obtain ⟨squarePositive, squareValues, squareBody, squareCallee, squareShape, squareTarget, squareValue, squarePost,
    squareArgs, squareCalled, squareRun, squareChecked, squareTail, squarePostEq⟩ :=
    Input.CallNormal.scoped_data first wPost "sq" (.comb [.one, .one]) (ofString "mul64x64") [localVar "w", localVar "w"] afterSquare returned tailRun
  have expectedSquareArgs : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) [localVar "w", localVar "w"] = some [.val (.word w), .val (.word w)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, firstW]
  have squareValuesEq := Option.some.inj (squareArgs.symm.trans expectedSquareArgs)
  rw [squareValuesEq] at squareCalled
  obtain ⟨squareEq, squareNext⟩ := Mul64.resume_value first squareTarget "sq" w w installed squareBody squareCallee squareShape squareCalled squareValue squareRun
  rw [squareNext] at squareTail
  let second := setVarHOLFinite (ofString "sq") (Mul64.value w w) {first with clock := first.clock - 1}
  have squareLocal : second.locals.lookup (ofString "sq") = some (Mul64.value w w) := by
    simp [second, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have secondW : second.locals.lookup (ofString "w") = some (.val (.word w)) := by
    simpa [second, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using firstW
  change returned = .val (.word (if (Mul64.parts w w).2 ≠ 0#64 then 18446744073709551615#64
    else SaturatingAdd.resultWord (w * 3#64) ((Mul64.parts w w).1 >>> (9 : Nat))))
  by_cases nonzero : (Mul64.parts w w).2 ≠ 0#64
  · have guardRun : evaluateHOLFiniteState second guard = (some (.returned (.val (.word 18446744073709551615#64))), emptyLocalsHOLFinite second) := by
      simp [guard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return, evalHOLExact, toExact, localVar,
        squareLocal, Mul64.value, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterSquare, WitnessRadix.StateSteps.stopped_sequence second _ guard afterGuard _ guardRun (Nat.le_refl _)] at squareTail
    have valueEq := congrArg Prod.fst squareTail
    rw [if_pos nonzero]
    exact PanSemResultExact.returned.inj (Option.some.inj valueEq.symm)
  · have guardRun : evaluateHOLFiniteState second guard = (none, second) := by
      simp [guard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        squareLocal, Mul64.value, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]
    rw [afterSquare, WitnessRadix.StateSteps.next_sequence second second guard afterGuard guardRun (Nat.le_refl _)] at squareTail
    have addCode := OriginalCodeEnvironment.arithmetic second.code installed .add_sat
    rw [ChargeWithMemory.add_signature] at addCode
    obtain ⟨a, b, inner, paid, arguments, lower, finish, finishEq⟩ := SaturatingAdd.normal_prefix second squarePost "a"
      [.panop .mul [localVar "w", .const 3#64], .shift .lsr (.rfield 0 (localVar "sq")) (.const 9#64)] (.return (localVar "a")) addCode returned squareTail
    have expected : evalListHOLFinite second (h := fun address => Classical.propDecidable (second.memaddrs address))
        [.panop .mul [localVar "w", .const 3#64], .shift .lsr (.rfield 0 (localVar "sq")) (.const 9#64)] =
        some [.val (.word (w * 3#64)), .val (.word ((Mul64.parts w w).1 >>> (9 : Nat)))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, secondW, squareLocal, Mul64.value,
        valueIsWord, valueWord, panOpHOL, wordShiftHOL]
    have argumentsEq := Option.some.inj (arguments.symm.trans expected)
    have aEq : a = w * 3#64 := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj argumentsEq).1)
    have bEq : b = (Mul64.parts w w).1 >>> (9 : Nat) := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj argumentsEq).2).1)
    let ready := WitnessRadix.QueryBranch.bind {second with clock := second.clock - 1} "a" (SaturatingAdd.resultWord a b)
    have aLocal : ready.locals.lookup (ofString "a") = some (.val (.word (SaturatingAdd.resultWord a b))) := bind_lookup_same _ _ _
    obtain ⟨read, finalEq⟩ := Input.return_normal ready inner (localVar "a") returned finish
    have actual : eval ready (localVar "a") = some (.val (.word (SaturatingAdd.resultWord a b))) := by
      simp [eval, evalHOLExact, toExact, localVar, aLocal]
    have result := Option.some.inj (read.symm.trans actual)
    rw [if_neg nonzero]
    simpa only [aEq, bEq] using result

theorem lower (size : BitVec 64) : 3 * (size.toNat / 32) ≤ (resultWord size).toNat := by
  let w := WordsOf.resultWord size
  have count := WordsOf.lower size
  have upper := WordsOf.upper size
  change size.toNat / 32 ≤ w.toNat at count
  change w.toNat ≤ 576460752303423487 at upper
  have product : (w * 3#64).toNat = 3 * w.toNat := by
    rw [BitVec.toNat_mul]
    change (w.toNat * 3) % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  change 3 * (size.toNat / 32) ≤ (if (Mul64.parts w w).2 ≠ 0#64 then 18446744073709551615#64
    else SaturatingAdd.resultWord (w * 3#64) ((Mul64.parts w w).1 >>> (9 : Nat))).toNat
  by_cases nonzero : (Mul64.parts w w).2 ≠ 0#64
  · rw [if_pos nonzero]
    change 3 * (size.toNat / 32) ≤ 18446744073709551615
    have bound := size.isLt
    omega
  · rw [if_neg nonzero]
    have covered : (w * 3#64).toNat ≤ (SaturatingAdd.resultWord (w * 3#64) ((Mul64.parts w w).1 >>> (9 : Nat))).toNat := SaturatingAdd.ge_left _ _
    rw [product] at covered
    change 3 * (size.toNat / 32) ≤ (SaturatingAdd.resultWord (w * 3#64) ((Mul64.parts w w).1 >>> (9 : Nat))).toNat
    omega

theorem zero : resultWord 0#64 = 0#64 := by
  simp [resultWord, WordsOf.zero, Mul64.parts, wordAddCarryHOL, SaturatingAdd.resultWord]

/-- Conditional byte ceiling supplied by a reachable memory-cost potential;
the global potential and byte-event total are not yet instantiated. -/
theorem byte_bound (size : BitVec 64) (cap : (resultWord size).toNat ≤ 16777216) : size.toNat ≤ 178956991 := by
  have covered := lower size
  omega

end InitECandidate.Solver.GasBudget.MemoryGasCost

#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.normal_value
#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.lower
#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.zero
#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.byte_bound
