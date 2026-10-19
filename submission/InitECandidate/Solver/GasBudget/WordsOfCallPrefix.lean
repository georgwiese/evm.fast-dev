import InitECandidate.Solver.GasBudget.WordsOfRange
import InitECandidate.Solver.Input.PricedReadOnlyPrefix

namespace InitECandidate.Solver.GasBudget.WordsOf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (installed : Input.OriginalCode.Installed source.code) (positive : 1 ≤ source.clock)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "words_of") values = some (actual, callee, shape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    ∃ (word : BitVec 64) (paid : Nat), word.toNat ≤ 576460752303423487 ∧ 1 ≤ paid ∧ paid ≤ 3 ∧ paid ≤ source.clock ∧
      Input.CallNormal.continuationEntry source target name returned = bind {source with clock := source.clock - paid} name word := by
  have code := original_code source.code installed
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "words_of") formals body .one code values actual callee shape called
  have actualRun := run
  rw [bodyEq] at actualRun
  obtain ⟨word, returnedEq, small⟩ := body_range (callEntryStateHOLFinite source callee) target returned actualRun
  obtain ⟨paid, nonzero, bounded, fits, next⟩ := Input.PricedReadOnlyPrefix.resume source target name (ofString "words_of")
    formals body .one 2 code (MemoryCostEffects.pure_words_of source.code installed) (MemoryCostEffects.price_words_of source.code installed)
    positive values actual callee shape called returned run
  exact ⟨word, paid, small, nonzero, bounded, fits, by simpa only [returnedEq, WitnessRadix.QueryBranch.bind] using next⟩

/-- Actual normal scoped words_of derives a bounded scalar, its paid clocks
and a real continuation with every nonlocal field retained. -/
theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "words_of") arguments continuation) = (some (.returned value), post)) :
    ∃ (word : BitVec 64) (paid : Nat) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      word.toNat ≤ 576460752303423487 ∧ 1 ≤ paid ∧ paid ≤ 3 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name word) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name .one _ arguments continuation value run
  obtain ⟨word, paid, small, nonzero, bounded, fits, next⟩ := resume source target name installed positive values actual callee shape called returned bodyRun
  exact ⟨word, paid, inner, small, nonzero, bounded, fits, by rw [← next]; exact tailRun, postEq⟩

/-- An actual exception following words_of comes from its genuine resumed
continuation; the unchanged helper is nonthrowing at every clock. -/
theorem exception_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (installed : Input.OriginalCode.Installed source.code)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "words_of") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ (word : BitVec 64) (paid : Nat) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      word.toNat ≤ 576460752303423487 ∧ 1 ≤ paid ∧ paid ≤ 3 ∧ paid ≤ source.clock ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name word) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name .one _ arguments continuation identifier payload run
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "words_of") formals body .one (original_code source.code installed)
      values actual callee shape called
    rw [bodyEq] at bodyRun
    exact (MemoryCostEffects.safe_words_of source.code installed (callEntryStateHOLFinite source callee) rfl identifier payload (congrArg Prod.fst bodyRun)).elim
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    obtain ⟨word, paid, small, nonzero, bounded, fits, next⟩ := resume source target name installed positive values actual callee shape called returned bodyRun
    exact ⟨word, paid, inner, small, nonzero, bounded, fits, by rw [← next]; exact tailRun, postEq⟩

end InitECandidate.Solver.GasBudget.WordsOf

#print axioms InitECandidate.Solver.GasBudget.WordsOf.resume
#print axioms InitECandidate.Solver.GasBudget.WordsOf.normal_prefix
#print axioms InitECandidate.Solver.GasBudget.WordsOf.exception_prefix
