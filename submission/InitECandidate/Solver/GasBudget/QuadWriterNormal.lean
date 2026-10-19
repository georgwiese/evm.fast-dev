import InitECandidate.Solver.GasBudget.QuadWriterFast

namespace InitECandidate.Solver.GasBudget.QuadWriter
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite MemoryWriter

theorem full_test : MemoryWriter.fastTest .quad = .cmp .equal (.op .and [localVar "out", .const 7#64]) (.const 0#64) := by
  simp only [MemoryWriter.fastTest, MemoryWriter.Kind.body, MemoryWriter.Kind.signature, MemoryWriter.Kind.original,
    Guest.guestFn_u256_to_be32, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, localVar]

set_option maxHeartbeats 1000000 in
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : U256Value.Words)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "out") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "a") = some (U256Value.tuple words)) (mapped : BytesMapped source pointer 32)
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source MemoryWriter.Kind.quad.body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 12 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 32 → post.memory query = source.memory query) := by
  have maskRead : eval source (.op .and [localVar "out", .const 7#64]) = some (.val (.word (pointer &&& 7#64))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, pointerLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
    rfl
  simp only [eval] at maskRead
  rw [MemoryWriter.guarded_body .quad (Or.inr rfl)] at run
  by_cases aligned : pointer &&& 7#64 = 0#64
  · have gate : evaluateHOLFiniteState source (.ite (MemoryWriter.fastTest .quad) (MemoryWriter.fast .quad) .skip) = evaluateHOLFiniteState source (MemoryWriter.fast .quad) := by
      rw [full_test, evaluateHOLFiniteState_ite, evalHOLExact, maskRead]
      simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, aligned]
    have whole : evaluateHOLFiniteState source (.seq (MemoryWriter.fast .quad) (MemoryWriter.slow .quad)) = (some (.returned returned), post) := by
      rw [evaluateHOLFiniteState_seq_line780]
      rwa [evaluateHOLFiniteState_seq_line780, gate] at run
    have actual := Input.NoFallthrough.returning_prefix source post (MemoryWriter.fast .quad) (MemoryWriter.slow .quad)
      (MemoryWriter.fast_stops .quad (Or.inr rfl)) returned whole
    obtain ⟨value, paid, bound, fits, clock, fields, away⟩ := fast_normal source post pointer installed pointerLocal mapped
      (AllocatedBytes.mask_aligned pointer aligned) returned actual
    exact ⟨value, paid, by omega, fits, clock, fields, away⟩
  · have gate : evaluateHOLFiniteState source (.ite (MemoryWriter.fastTest .quad) (MemoryWriter.fast .quad) .skip) = (none, source) := by
      rw [full_test, evaluateHOLFiniteState_ite, evalHOLExact, maskRead]
      simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, aligned, evaluateHOLFiniteState_skip]
    rw [StateSteps.next_sequence source source _ (MemoryWriter.slow .quad) gate (Nat.le_refl _)] at run
    exact slow_normal source post pointer words installed pointerLocal valueLocal mapped returned run

theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "u256_to_be32") =
    some ([(ofString "a", U256Value.tupleShape), (ofString "out", .one)], MemoryWriter.Kind.quad.body, .one) := by
  simpa only [MemoryWriter.Kind.name, MemoryWriter.Kind.signature, MemoryWriter.Kind.original, Guest.guestFn_u256_to_be32,
    MemoryWriter.Kind.body, paramToHOL, shapeToHOL, U256Value.tupleShape, List.map_cons, List.map_nil]
    using MemoryWriter.original_code .quad code installed

theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : U256Value.Words)
    (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [U256Value.tuple words, .val (.word pointer)])
    (mapped : BytesMapped source pointer 32)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "u256_to_be32") arguments) = (none, post)) :
    ∃ paid : Nat, paid ≤ 13 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      post = {source with memory := post.memory, clock := source.clock - paid} ∧
      (∀ query, BytesAway pointer query 32 → post.memory query = source.memory query) := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    Input.CallNormal.ignored_data source post (ofString "u256_to_be32") arguments run
  have valuesEq := Option.some.inj (args.symm.trans argsRead)
  rw [valuesEq] at called
  obtain ⟨bodyEq, shapeEq, valueCell, pointerCell⟩ := Input.CallNormal.binary_lookup_known source.code.lookup (ofString "u256_to_be32")
    (ofString "a") (ofString "out") U256Value.tupleShape .one MemoryWriter.Kind.quad.body .one (U256Value.tuple words) (.val (.word pointer))
    actual callee shape (by decide) (original_code source.code installed) called
  rw [bodyEq] at bodyRun
  obtain ⟨valueEq, paid, bound, funded, clock, effect, away⟩ :=
    normal (callEntryStateHOLFinite source callee) target pointer words installed pointerCell valueCell mapped returned bodyRun
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

end InitECandidate.Solver.GasBudget.QuadWriter

#print axioms InitECandidate.Solver.GasBudget.QuadWriter.normal
#print axioms InitECandidate.Solver.GasBudget.QuadWriter.call_normal
