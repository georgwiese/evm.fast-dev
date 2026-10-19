import InitECandidate.Solver.GasBudget.RevertStores
import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.SatWordExceptionPrefix

namespace InitECandidate.Solver.GasBudget.RevertOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1000000 in
theorem suffix_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch : BitVec 64) (start size : U256Value.Words)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (ofString "size") = some (U256Value.tuple size))
    (shape : source.eshapes.lookup (ofString "EvmErr") = some .one) (identifier : MlS) (payload : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterExpansion = (some (.exception identifier payload), post)) :
    2 ≤ source.clock ∧ identifier = ofString "EvmErr" ∧ payload = .val (.word 1#64) ∧ post.clock = source.clock - 2 ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      post.globals = source.globals ∧ regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      post.memory (frame + 16#64) = source.memory (frame + 16#64) ∧
      post.memory = WordWrites.write source.memory (writes frame base (SatWord.resultWord start) (SatWord.resultWord size)) ∧
      (∀ query, query ≠ frame + 120#64 → query ≠ frame + 128#64 → post.memory query = source.memory query) := by
  have sizeRead : eval source (localVar "size") = some (U256Value.tuple size) := by simp [eval, localVar, evalHOLExact, toExact, sizeLocal]
  obtain ⟨paidN, first, firstPost, positiveN, boundN, fitsN, firstEq, firstFields, firstRun, firstScope⟩ :=
    SatWord.exception_prefix source post view.installed "n" (localVar "size") afterSize size identifier payload sizeRead normal
  have paidNEq : paidN = 1 := by change paidN ≤ 1 at boundN; omega
  subst paidN
  have firstView := view.after_erase firstFields
  have firstStart := (Input.KnownUnaryPrefix.lookup_other firstEq "start" (by decide)).trans startLocal
  have firstN := Input.KnownUnaryPrefix.lookup_same firstEq
  have startRead : eval first (localVar "start") = some (U256Value.tuple start) := by simp [eval, localVar, evalHOLExact, toExact, firstStart]
  obtain ⟨paidS, ready, inner, positiveS, boundS, fitsS, readyEq, readyFields, run, secondScope⟩ :=
    SatWord.exception_prefix first firstPost firstView.installed "s" (localVar "start") stores start identifier payload startRead firstRun
  have paidSEq : paidS = 1 := by change paidS ≤ 1 at boundS; omega
  subst paidS
  have readyView := firstView.after_erase readyFields
  have sCell := Input.KnownUnaryPrefix.lookup_same readyEq
  have nCell := (Input.KnownUnaryPrefix.lookup_other readyEq "n" (by decide)).trans firstN
  have readyShape : ready.eshapes.lookup (ofString "EvmErr") = some .one := by rw [readyEq, firstEq]; exact shape
  obtain ⟨actualId, actualPayload, innerEq⟩ := stores_exception ready inner frame base length capacity pointer scratch
    (SatWord.resultWord start) (SatWord.resultWord size) readyView sCell nCell readyShape identifier payload run
  have firstClock : first.clock = source.clock - 1 := by rw [firstEq]; rfl
  have readyClock : ready.clock = first.clock - 1 := by rw [readyEq]; rfl
  have postFields : Input.LocalEffects.erase post = Input.LocalEffects.erase
      {source with memory := WordWrites.write source.memory (writes frame base (SatWord.resultWord start) (SatWord.resultWord size))} := by
    rw [firstScope, secondScope, innerEq, readyEq, firstEq]
    rfl
  have memory : post.memory = WordWrites.write source.memory (writes frame base (SatWord.resultWord start) (SatWord.resultWord size)) := by
    have retained := congrArg PanSemStateFiniteExact.memory postFields
    exact retained
  have globals : post.globals = source.globals := by
    have retained := congrArg PanSemStateFiniteExact.globals postFields
    exact retained
  have away (query : BitVec 64) (notOutput : query ≠ frame + 120#64) (notSize : query ≠ frame + 128#64) : post.memory query = source.memory query := by
    rw [memory]
    exact writes_away source.memory frame base (SatWord.resultWord start) (SatWord.resultWord size) _ notOutput notSize
  have memoryView := view.with_memory (WordWrites.write source.memory (writes frame base (SatWord.resultWord start) (SatWord.resultWord size)))
    ((writes_away source.memory frame base (SatWord.resultWord start) (SatWord.resultWord size) _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))).trans view.baseCell)
    ((writes_away source.memory frame base (SatWord.resultWord start) (SatWord.resultWord size) _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))).trans view.lengthCell)
    ((writes_away source.memory frame base (SatWord.resultWord start) (SatWord.resultWord size) _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))).trans view.capacityCell)
  refine ⟨by rw [firstClock] at fitsS; omega, actualId, actualPayload, ?_, memoryView.after_erase postFields, globals, ?_, ?_, ?_, memory, away⟩
  · rw [firstScope, secondScope, innerEq]
    change ready.clock = _
    rw [readyClock, firstClock]
    omega
  · unfold regularBudget wordAt
    rw [away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)),
      away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)),
      away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))]
  · exact away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))
  · exact away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide))

end InitECandidate.Solver.GasBudget.RevertOpcode

#print axioms InitECandidate.Solver.GasBudget.RevertOpcode.suffix_exception
