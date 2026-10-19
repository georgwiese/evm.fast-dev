import InitECandidate.Solver.GasBudget.U256FromBeCall
import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.MemoryOpcodeProgram
import InitECandidate.Solver.GasBudget.DirectStackOpcode

namespace InitECandidate.Solver.GasBudget.MemoryLoad
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def address : ExpHOL 64 := .op .add [frameLoad 24#64, localVar "s"]
def afterScalar : ProgHOL 64 := .decCall (ofString "v") U256Value.tupleShape (ofString "u256_from_be")
  [address, .const 32#64] (StackPush.finish [localVar "v"])

theorem suffix_shape : MemoryOpcode.Kind.mload.suffix = .decCall (ofString "s") .one (ofString "sat_word") [localVar "start"] afterScalar := by
  simp only [MemoryOpcode.Kind.suffix, MemoryOpcode.Kind.body, MemoryOpcode.Kind.original, MemoryOpcode.Kind.names,
    Guest.guestFn_op_mload, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, Option.map_none, afterScalar, address, StackPush.finish, U256Value.tupleShape,
    localVar, frameLoad, frameAddress]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem suffix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch : BitVec 64) (start : U256Value.Words)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (entry : DirectStackOpcode.Entry source frame) (room : entry.sp < entry.capacity)
    (memoryApart : ∀ offset ∈ ([24, 32, 40] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (entry.base + entry.sp * 32#64) + BitVec.ofNat 64 (8 * index))
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source MemoryOpcode.Kind.mload.suffix = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ paid : Nat, paid ≤ 36 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧ regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      post.memory (frame + 16#64) = .word (entry.sp + 1#64) ∧ (wordAt post.memory (frame + 16#64)).toNat = entry.sp.toNat + 1 ∧
      (∀ query, query ≠ frame + 0#64 → query ≠ frame + 16#64 →
        (∀ index < 4, query ≠ (entry.base + entry.sp * 32#64) + BitVec.ofNat 64 (8 * index)) → post.memory query = source.memory query) := by
  rw [suffix_shape] at normal
  have read : eval source (localVar "start") = some (U256Value.tuple start) := by simp [eval, localVar, evalHOLExact, toExact, startLocal]
  obtain ⟨scalarPaid, first, firstPost, positive, bound, fits, firstEq, firstFields, firstRun, firstScope⟩ :=
    MemoryCostCalls.normal .sat source post "s" (localVar "start") afterScalar start returned view.installed read normal
  have scalarPaidEq : scalarPaid = 1 := by change scalarPaid ≤ 1 at bound; omega
  subst scalarPaid
  have firstView := view.after_erase firstFields
  have scalar := Input.KnownUnaryPrefix.lookup_same firstEq
  have baseRead := frame_read first frame 24#64 base firstView.ev (firstView.mapped 24 (by simp)) firstView.baseCell
  have args : evalListHOLFinite first (h := fun query => Classical.propDecidable (first.memaddrs query)) [address, .const 32#64] =
      some [.val (.word (base + SatWord.resultWord start)), .val (.word (BitVec.ofNat 64 32))] := by
    simp only [eval] at baseRead
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, address, baseRead, localVar, scalar, MemoryCostCalls.Kind.result,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨readPaid, words, ready, inner, readPositive, readBound, readFits, readyEq, readyFields, finishRun, secondScope⟩ :=
    U256FromBe.normal_prefix first firstPost firstView.installed (base + SatWord.resultWord start) 32 (by decide) "v"
      [address, .const 32#64] (StackPush.finish [localVar "v"]) returned args firstRun
  have allFields := readyFields.trans firstFields
  have memory : ready.memory = source.memory := Input.LocalEffects.memory_of_erase source ready allFields
  have code : ready.code = source.code := Input.LocalEffects.code_of_erase source ready allFields
  have globals := congrArg PanSemStateFiniteExact.globals allFields
  have mapped := congrArg PanSemStateFiniteExact.memaddrs allFields
  change ready.globals = source.globals at globals
  change ready.memaddrs = source.memaddrs at mapped
  have slotApart : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (entry.base + entry.sp * 32#64) + BitVec.ofNat 64 (8 * index) := by
    intro offset member index inside
    have actual := entry.separate entry.sp.toNat (BitVec.lt_def.mp room) offset member index inside
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using actual
  obtain ⟨finishFits, value, finishClock, finishFrame, budget, used, finalSP, depth, finishAway⟩ :=
    StackPush.finish_normal ready inner frame entry.base entry.sp entry.capacity [localVar "v"]
      (by rw [code]; exact entry.pushCode) (by rw [code]; exact entry.pcCode) (by rw [globals]; exact entry.ev)
      (by rw [memory]; exact entry.spCell) (by rw [memory]; exact entry.capCell) (by rw [mapped]; exact entry.baseMapped)
      (by rw [memory]; exact entry.baseCell) room entry.capBound slotApart returned finishRun
  have firstClock : first.clock = source.clock - 1 := by rw [firstEq]; rfl
  have readyClock : ready.clock = source.clock - 1 - readPaid := by rw [readyEq]; change first.clock - readPaid = _; rw [firstClock]
  have postMemory : post.memory = inner.memory := by rw [firstScope, secondScope]; rfl
  have postClock : post.clock = inner.clock := by rw [firstScope, secondScope]; rfl
  have away : ∀ query, query ≠ frame + 0#64 → query ≠ frame + 16#64 →
      (∀ index < 4, query ≠ (entry.base + entry.sp * 32#64) + BitVec.ofNat 64 (8 * index)) → post.memory query = source.memory query := by
    intro query notPC notSP notSlot
    rw [postMemory, finishAway query notPC notSP notSlot, memory]
  have memoryView := view.with_memory post.memory
    ((away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)) (memoryApart 24 (by simp))).trans view.baseCell)
    ((away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)) (memoryApart 32 (by simp))).trans view.lengthCell)
    ((away _ (offsets_ne frame _ _ (by decide)) (offsets_ne frame _ _ (by decide)) (memoryApart 40 (by simp))).trans view.capacityCell)
  have postFields : Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} := by
    have erasedFinish := congrArg Input.LocalEffects.erase finishFrame
    have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => Input.LocalEffects.erase {state with memory := inner.memory}) allFields
    rw [firstScope, secondScope]
    exact erasedFinish.trans lifted
  refine ⟨value, 1 + readPaid + 2, by change readPaid ≤ 33 at readBound; omega, ?_, ?_, memoryView.after_erase postFields, ?_, ?_, ?_, ?_, away⟩
  · rw [readyClock] at finishFits
    rw [firstClock] at readFits
    omega
  · rw [postClock, finishClock, readyClock]
    omega
  · rw [postMemory, budget, memory]
  · rw [postMemory, used, memory]
  · rw [postMemory]; exact finalSP
  · rw [postMemory]; exact depth

end InitECandidate.Solver.GasBudget.MemoryLoad

#print axioms InitECandidate.Solver.GasBudget.MemoryLoad.suffix_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryLoad.suffix_normal
