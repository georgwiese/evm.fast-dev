import InitECandidate.Solver.GasBudget.QuadWriterNormal
import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.MemoryOpcodeProgram
import InitECandidate.Solver.GasBudget.PcAddNormal

namespace InitECandidate.Solver.GasBudget.MemoryStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def writeArgs : List (ExpHOL 64) := [localVar "value", .op .add [frameLoad 24#64, localVar "s"]]
def finish : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) MemoryExtend.returnZero
def afterScalar : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "u256_to_be32") writeArgs) finish

theorem suffix_shape : MemoryOpcode.Kind.mstore.suffix = .decCall (ofString "s") .one (ofString "sat_word") [localVar "start"] afterScalar := by
  simp only [MemoryOpcode.Kind.suffix, MemoryOpcode.Kind.body, MemoryOpcode.Kind.original, MemoryOpcode.Kind.names,
    Guest.guestFn_op_mstore, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, Option.map_none, afterScalar, writeArgs, finish, MemoryExtend.returnZero,
    localVar, frameLoad, frameAddress]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem suffix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch : BitVec 64) (start value : U256Value.Words)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (valueLocal : source.locals.lookup (ofString "value") = some (U256Value.tuple value))
    (range : (SatWord.resultWord start).toNat + 32 ≤ length.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source MemoryOpcode.Kind.mstore.suffix = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 15 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧ regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 0#64 → post.memory query = source.memory query) := by
  rw [suffix_shape] at normal
  have read : eval source (localVar "start") = some (U256Value.tuple start) := by simp [eval, evalHOLExact, toExact, localVar, startLocal]
  obtain ⟨scalarPaid, ready, inner, positive, bound, fits, readyEq, fields, run, scopeEq⟩ :=
    MemoryCostCalls.normal .sat source post "s" (localVar "start") afterScalar start returned view.installed read normal
  have paidEq : scalarPaid = 1 := by change scalarPaid ≤ 1 at bound; omega
  subst scalarPaid
  have readyView := view.after_erase fields
  have scalar := Input.KnownUnaryPrefix.lookup_same readyEq
  have readyValue := (Input.KnownUnaryPrefix.lookup_other readyEq "value" (by decide)).trans valueLocal
  have baseRead := frame_read ready frame 24#64 base readyView.ev (readyView.mapped 24 (by simp)) readyView.baseCell
  have args : evalListHOLFinite ready (h := fun query => Classical.propDecidable (ready.memaddrs query)) writeArgs =
      some [U256Value.tuple value, .val (.word (base + SatWord.resultWord start))] := by
    simp only [eval] at baseRead
    simp [writeArgs, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, scalar, readyValue,
      MemoryCostCalls.Kind.result, baseRead, valueIsWord, valueWord, wordOpHOL, wordOp]
  have mapped : MemoryWriter.BytesMapped ready (base + SatWord.resultWord start) 32 := by
    intro offset inside
    have owned := (readyView.byte_owned (SatWord.resultWord start) 32 offset range inside).1
    simpa [byteAddress] using owned
  have safe : Input.LocalPrefix (ofString "s") (.call (some (none, none)) (ofString "u256_to_be32") writeArgs) := .call none _ _ (by simp)
  obtain ⟨written, writeRun, finishRun, saved⟩ := safe.normal_continue ready inner finish returned run
  obtain ⟨writePaid, writeBound, writeFits, writeClock, writeFrame, writeAway⟩ :=
    QuadWriter.call_normal ready written (base + SatWord.resultWord start) value readyView.installed writeArgs args mapped writeRun
  have bufferAway (query : BitVec 64) (outside : Arenas.Outside base scratch query) : written.memory query = ready.memory query := by
    apply writeAway query
    intro offset inside
    have apart := readyView.byte_away (SatWord.resultWord start) 32 offset range inside query outside
    simpa [byteAddress] using apart
  have writtenMemoryView := readyView.with_memory written.memory
    ((bufferAway _ (readyView.header_outside 24 (by decide))).trans readyView.baseCell)
    ((bufferAway _ (readyView.header_outside 32 (by decide))).trans readyView.lengthCell)
    ((bufferAway _ (readyView.header_outside 40 (by decide))).trans readyView.capacityCell)
  have writtenView := writtenMemoryView.after_erase (show Input.LocalEffects.erase written = Input.LocalEffects.erase {ready with memory := written.memory} by rw [writeFrame]; rfl)
  have pcSafe : Input.LocalPrefix (ofString "s") (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) := .call none _ _ (by simp)
  obtain ⟨advanced, pcRun, returnRun, retained⟩ := pcSafe.normal_continue written inner MemoryExtend.returnZero returned finishRun
  obtain ⟨pc, pcFits, pcClock, pcMapped, pcCell, advancedEq, pcBudget, pcUsed⟩ := PcAdd.call_normal written advanced frame 1#64 [.const 1#64] rfl
    (OriginalCodeEnvironment.pc_add written.code writtenView.installed) writtenView.ev pcRun
  obtain ⟨returnRead, finalEq⟩ := Input.return_normal advanced inner (.const 0#64) returned returnRun
  have valueEq : returned = .val (.word 0#64) := (Option.some.inj returnRead).symm
  have readyClock : ready.clock = source.clock - 1 := by rw [readyEq]; rfl
  have memory := Input.LocalEffects.memory_of_erase source ready fields
  have outside (query : BitVec 64) (owned : Arenas.Outside base scratch query) (notPC : query ≠ frame + 0#64) : post.memory query = source.memory query := by
    rw [scopeEq, finalEq, advancedEq]
    change StoreWord.put written.memory (frame + 0#64) _ query = _
    rw [StoreWord.put, if_neg notPC, bufferAway query owned, memory]
  have pcView : MemoryExtend.View advanced frame base length capacity pointer scratch := by
    have next := writtenView.with_memory (StoreWord.put written.memory (frame + 0#64) (pc + 1#64))
      (FrameField.put_other written.memory frame 0#64 (pc + 1#64) 24#64 (by decide) |>.trans writtenView.baseCell)
      (FrameField.put_other written.memory frame 0#64 (pc + 1#64) 32#64 (by decide) |>.trans writtenView.lengthCell)
      (FrameField.put_other written.memory frame 0#64 (pc + 1#64) 40#64 (by decide) |>.trans writtenView.capacityCell)
    exact next.after_erase (by rw [advancedEq]; rfl)
  refine ⟨valueEq, writePaid + 2, by omega, ?_, ?_, pcView.after_erase (by rw [scopeEq, finalEq]; rfl), ?_, ?_, outside⟩
  · rw [writeClock, readyClock] at pcFits
    rw [readyClock] at writeFits
    omega
  · rw [scopeEq, finalEq]
    change advanced.clock = _
    rw [pcClock, writeClock, readyClock]
    omega
  · unfold regularBudget wordAt
    rw [outside _ (view.header_outside 64 (by decide)) (offsets_ne frame _ _ (by decide)),
      outside _ (view.header_outside 184 (by decide)) (offsets_ne frame _ _ (by decide)),
      outside _ (view.header_outside 192 (by decide)) (offsets_ne frame _ _ (by decide))]
  · exact outside _ (view.header_outside 184 (by decide)) (offsets_ne frame _ _ (by decide))

end InitECandidate.Solver.GasBudget.MemoryStore

#print axioms InitECandidate.Solver.GasBudget.MemoryStore.suffix_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryStore.suffix_normal
