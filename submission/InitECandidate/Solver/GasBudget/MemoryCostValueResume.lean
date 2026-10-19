import InitECandidate.Solver.GasBudget.MemoryCostNormalValues
import InitECandidate.Solver.GasBudget.Mul64Value
import InitECandidate.Solver.Input.ScalarPairLookupShape
import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem WordsOf.resume_value (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (n : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "words_of") [.val (.word n)] = some (actual, callee, shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    returned = .val (.word (WordsOf.resultWord n)) ∧ 1 + WordsOf.price n ≤ source.clock ∧
      Input.CallNormal.continuationEntry source target name returned =
        WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1 - WordsOf.price n} name (WordsOf.resultWord n) := by
  obtain ⟨argument, valuesEq, bodyEq, shapeEq, typed, binding⟩ := Input.CallNormal.unary_lookup_data source.code.lookup
    (ofString "words_of") (ofString "n") .one WordsOf.body .one (WordsOf.original_code source.code installed) [.val (.word n)] actual callee shape called
  have argumentEq : argument = .val (.word n) := (List.cons.inj valuesEq).1.symm
  rw [argumentEq] at binding
  rw [bodyEq] at run
  obtain ⟨returnedEq, funded, clock, frame⟩ := WordsOf.normal (callEntryStateHOLFinite source callee) target n installed binding returned run
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - WordsOf.price n} at callerFrame
  have positive : 1 ≤ WordsOf.price n := by unfold WordsOf.price; omega
  change WordsOf.price n ≤ source.clock - 1 at funded
  refine ⟨returnedEq, by omega, ?_⟩
  simp only [Input.CallNormal.continuationEntry, returnedEq, callerFrame, WitnessRadix.QueryBranch.bind]

theorem Mul64.original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "mul64x64") = some ([(ofString "a", .one), (ofString "b", .one)], Mul64.body, .comb [.one, .one]) := by
  simpa only [Mul64.body, ArithmeticEffects.Kind.name, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature,
    ArithmeticEffects.Kind.original, Guest.guestFn_mul64x64, shapeToHOL, List.map_cons, List.map_nil, paramToHOL]
    using OriginalCodeEnvironment.arithmetic code installed .mul64x64

theorem Mul64.resume_value (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (a b : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "mul64x64") [.val (.word a), .val (.word b)] = some (actual, callee, shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    returned = Mul64.value a b ∧
      Input.CallNormal.continuationEntry source target name returned = setVarHOLFinite (ofString name) (Mul64.value a b) {source with clock := source.clock - 1} := by
  obtain ⟨argA, argB, valuesEq, bodyEq, shapeEq, aLocal, bLocal⟩ := Input.CallNormal.scalar_pair_lookup_shape source.code.lookup
    (ofString "mul64x64") Mul64.body (.comb [.one, .one]) (Mul64.original_code source.code installed)
    [.val (.word a), .val (.word b)] actual callee shape called
  have aEq : argA = a := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj valuesEq).1.symm)
  have bEq : argB = b := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj valuesEq).2).1.symm)
  subst argA
  subst argB
  rw [bodyEq] at run
  obtain ⟨expected, executed, frame⟩ := Mul64.execute (callEntryStateHOLFinite source callee) a b installed aLocal bLocal
  have same := run.symm.trans executed
  have returnedEq : returned = Mul64.value a b := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst same
  have targetEq := congrArg Prod.snd same
  change target = expected at targetEq
  rw [← targetEq] at frame
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  change {target with locals := source.locals} = {source with clock := source.clock - 1} at callerFrame
  exact ⟨returnedEq, by simp only [Input.CallNormal.continuationEntry, returnedEq, callerFrame]⟩

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.WordsOf.resume_value
#print axioms InitECandidate.Solver.GasBudget.Mul64.resume_value
