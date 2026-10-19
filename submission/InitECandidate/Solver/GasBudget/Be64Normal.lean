import InitECandidate.Solver.GasBudget.Be64Fast
import InitECandidate.Solver.GasBudget.Be64Slow
import InitECandidate.Solver.Input.StoppingPrefix
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.GasBudget.MemoryWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem be64_test : fastTest .be64 = .cmp .equal (.op .and [localVar "p", .const 7#64]) (.const 0#64) := by
  simp only [fastTest, Kind.body, Kind.signature, Kind.original, Guest.guestFn_st_be64, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]

set_option maxHeartbeats 1000000 in
theorem be64_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "v") = some (.val (.word value))) (mapped : BytesMapped source pointer 8)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source Kind.be64.body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 2 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 8 → post.memory query = source.memory query) := by
  have maskRead : eval source (.op .and [localVar "p", .const 7#64]) = some (.val (.word (pointer &&& 7#64))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, pointerLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
    rfl
  simp only [eval] at maskRead
  rw [guarded_body .be64 (Or.inl rfl)] at normal
  by_cases aligned : pointer &&& 7#64 = 0#64
  · have gate : evaluateHOLFiniteState source (.ite (fastTest .be64) (fast .be64) .skip) = evaluateHOLFiniteState source (fast .be64) := by
      rw [be64_test, evaluateHOLFiniteState_ite]
      rw [evalHOLExact, maskRead]
      simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, aligned]
    have fastWhole : evaluateHOLFiniteState source (.seq (fast .be64) (slow .be64)) = (some (.returned returned), post) := by
      rw [evaluateHOLFiniteState_seq_line780]
      rwa [evaluateHOLFiniteState_seq_line780, gate] at normal
    have fastRun := Input.NoFallthrough.returning_prefix source post (fast .be64) (slow .be64) (fast_stops .be64 (Or.inl rfl)) returned fastWhole
    have key : panByteAlignHOL (width := 64) pointer = pointer := by
      apply BitVec.eq_of_toNat_eq
      rw [AllocatedBytes.aligned_number]
      have division := Nat.mod_add_div pointer.toNat 8
      have remainder := AllocatedBytes.mask_aligned pointer aligned
      omega
    have pointerMapped : source.memaddrs pointer := by simpa [key] using mapped 0 (by decide)
    obtain ⟨valueEq, funded, clock, fields, word, memory⟩ := be64_fast_normal source post pointer installed pointerLocal pointerMapped returned fastRun
    refine ⟨valueEq, 1, by decide, funded, clock, fields, ?_⟩
    intro query away
    have different : query ≠ pointer := by simpa [key] using away 0 (by decide)
    rw [memory]
    exact if_neg different
  · have gate : evaluateHOLFiniteState source (.ite (fastTest .be64) (fast .be64) .skip) = (none, source) := by
      rw [be64_test, evaluateHOLFiniteState_ite]
      rw [evalHOLExact, maskRead]
      simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, aligned, evaluateHOLFiniteState_skip]
    rw [StateSteps.next_sequence source source _ (slow .be64) gate (Nat.le_refl _)] at normal
    obtain ⟨valueEq, funded, clock, fields, away⟩ := be64_slow_normal source post pointer value installed pointerLocal valueLocal mapped returned normal
    exact ⟨valueEq, 2, by decide, funded, clock, fields, away⟩

theorem be64_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "st_be64") = some ([(ofString "p", .one), (ofString "v", .one)], Kind.be64.body, .one) := by
  simpa only [Kind.name, Kind.signature, Kind.original, Guest.guestFn_st_be64, Kind.body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil]
    using original_code .be64 code installed

theorem be64_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [.val (.word pointer), .val (.word value)])
    (mapped : BytesMapped source pointer 8)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "st_be64") arguments) = (none, post)) :
    ∃ paid : Nat, paid ≤ 3 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      post = {source with memory := post.memory, clock := source.clock - paid} ∧
      (∀ query, BytesAway pointer query 8 → post.memory query = source.memory query) := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "st_be64") arguments normal
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨bodyEq, shapeEq, pointerCell, valueCell⟩ := Input.CallNormal.binary_lookup_known source.code.lookup (ofString "st_be64")
    (ofString "p") (ofString "v") .one .one Kind.be64.body .one (.val (.word pointer)) (.val (.word value))
    actual callee shape (by decide) (be64_code source.code installed) called
  rw [bodyEq] at bodyRun
  obtain ⟨valueEq, paid, bound, funded, clock, effect, away⟩ :=
    be64_normal (callEntryStateHOLFinite source callee) target pointer value installed pointerCell valueCell mapped returned bodyRun
  change paid ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - paid at clock
  have frame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) effect
  change {target with locals := source.locals} = {source with memory := target.memory, clock := target.clock} at frame
  have postClock : post.clock = source.clock - (paid + 1) := by rw [postEq]; change target.clock = _; rw [clock]; omega
  refine ⟨paid + 1, by omega, by omega, postClock, ?_, ?_⟩
  · have same := postEq.trans frame
    have memory := congrArg PanSemStateFiniteExact.memory postEq
    change post.memory = target.memory at memory
    rw [← memory] at same
    have targetClock : target.clock = post.clock := (congrArg PanSemStateFiniteExact.clock postEq).symm
    rw [targetClock, postClock] at same
    exact same
  · intro query outside
    rw [postEq]
    exact away query outside

end InitECandidate.Solver.GasBudget.MemoryWriter

#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_normal
#print axioms InitECandidate.Solver.GasBudget.MemoryWriter.be64_call_normal
