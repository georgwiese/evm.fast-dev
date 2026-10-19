import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.MemoryOpcodeProgram
import InitECandidate.Solver.GasBudget.PcAddNormal

namespace InitECandidate.Solver.GasBudget.MemoryStore8
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

def byteAddressExpression : ExpHOL 64 := .op .add [frameLoad 24#64, localVar "s"]
def byteValueExpression : ExpHOL 64 := .op .and [.rfield 0 (localVar "value"), .const 255#64]
def storeByte : ProgHOL 64 := .storeByte byteAddressExpression byteValueExpression
def finish : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) MemoryExtend.returnZero
def afterScalar : ProgHOL 64 := .seq storeByte finish

theorem suffix_shape : MemoryOpcode.Kind.mstore8.suffix = .decCall (ofString "s") .one (ofString "sat_word") [localVar "start"] afterScalar := by
  simp only [MemoryOpcode.Kind.suffix, MemoryOpcode.Kind.body, MemoryOpcode.Kind.original, MemoryOpcode.Kind.names,
    Guest.guestFn_op_mstore8, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, Option.map_none, afterScalar, storeByte,
    byteAddressExpression, byteValueExpression, finish, MemoryExtend.returnZero, localVar, frameLoad, frameAddress]

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem suffix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch : BitVec 64) (start value : U256Value.Words)
    (view : MemoryExtend.View source frame base length capacity pointer scratch)
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (valueLocal : source.locals.lookup (ofString "value") = some (U256Value.tuple value))
    (range : (SatWord.resultWord start).toNat + 1 ≤ length.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source MemoryOpcode.Kind.mstore8.suffix = (some (.returned returned), post)) :
    2 ≤ source.clock ∧ returned = .val (.word 0#64) ∧ post.clock = source.clock - 2 ∧
      MemoryExtend.View post frame base length capacity pointer scratch ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      post.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 0#64 → post.memory query = source.memory query) := by
  rw [suffix_shape] at normal
  have read : eval source (localVar "start") = some (U256Value.tuple start) := by simp [eval, evalHOLExact, toExact, localVar, startLocal]
  obtain ⟨paid, ready, inner, positive, bound, fits, readyEq, fields, run, scopeEq⟩ :=
    MemoryCostCalls.normal .sat source post "s" (localVar "start") afterScalar start returned view.installed read normal
  have paidEq : paid = 1 := by change paid ≤ 1 at bound; omega
  subst paid
  have readyView := view.after_erase fields
  have readyScalar := Input.KnownUnaryPrefix.lookup_same readyEq
  have readyValue := (Input.KnownUnaryPrefix.lookup_other readyEq "value" (by decide)).trans valueLocal
  have baseRead := frame_read ready frame 24#64 base readyView.ev (readyView.mapped 24 (by simp)) readyView.baseCell
  have addressRead : eval ready byteAddressExpression = some (.val (.word (base + SatWord.resultWord start))) := by
    simp only [eval] at baseRead
    simp [eval, byteAddressExpression, evalHOLExact, evalListHOLExact, toExact, baseRead, localVar, readyScalar,
      MemoryCostCalls.Kind.result, valueIsWord, valueWord, wordOpHOL, wordOp]
  have valueRead : eval ready byteValueExpression = some (.val (.word ((value 0) &&& 255#64))) := by
    simp [eval, byteValueExpression, evalHOLExact, evalListHOLExact, toExact, localVar, readyValue, U256Value.tuple,
      valueIsWord, valueWord, wordOpHOL, wordOp]
    rfl
  have mapped : ready.memaddrs (panByteAlignHOL (width := 64) (base + SatWord.resultWord start)) := by
    have owned := (readyView.byte_owned (SatWord.resultWord start) 1 0 range (by decide)).1
    simpa [byteAddress] using owned
  let byteMemory := ByteStore.put ready.memory ready.be (base + SatWord.resultWord start) (BitVec.ofNat 8 ((value 0) &&& 255#64).toNat)
  let stored := {ready with memory := byteMemory}
  have storeRun := ByteStore.execute_word ready byteAddressExpression byteValueExpression (base + SatWord.resultWord start) ((value 0) &&& 255#64) addressRead valueRead mapped
  rw [afterScalar, StateSteps.next_sequence ready stored storeByte finish storeRun (Nat.le_refl _)] at run
  have byteAway (query : BitVec 64) (outside : Arenas.Outside base scratch query) : byteMemory query = ready.memory query := by
    apply ByteStore.away
    have away := readyView.byte_away (SatWord.resultWord start) 1 0 range (by decide) query outside
    simpa [byteAddress] using away
  have byteView : MemoryExtend.View stored frame base length capacity pointer scratch := readyView.with_memory byteMemory
    ((byteAway _ (readyView.header_outside 24 (by decide))).trans readyView.baseCell)
    ((byteAway _ (readyView.header_outside 32 (by decide))).trans readyView.lengthCell)
    ((byteAway _ (readyView.header_outside 40 (by decide))).trans readyView.capacityCell)
  have pcSafe : Input.LocalPrefix (ofString "s") (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) := .call none _ _ (by simp)
  obtain ⟨advanced, pcRun, returnRun, saved⟩ := pcSafe.normal_continue stored inner MemoryExtend.returnZero returned run
  obtain ⟨pc, pcFits, pcClock, pcMapped, pcCell, advancedEq, pcBudget, pcUsed⟩ := PcAdd.call_normal stored advanced frame 1#64 [.const 1#64] rfl
    (OriginalCodeEnvironment.pc_add stored.code byteView.installed) byteView.ev pcRun
  obtain ⟨returnRead, finalEq⟩ := Input.return_normal advanced inner (.const 0#64) returned returnRun
  have result : returned = .val (.word 0#64) := by simpa [eval, evalHOLExact] using (Option.some.inj returnRead).symm
  have readyClock : ready.clock = source.clock - 1 := by rw [readyEq]; rfl
  have sourceMemory : ready.memory = source.memory := Input.LocalEffects.memory_of_erase source ready fields
  have outside (query : BitVec 64) (owned : Arenas.Outside base scratch query) (notPC : query ≠ frame + 0#64) : post.memory query = source.memory query := by
    rw [scopeEq, finalEq, advancedEq]
    change StoreWord.put byteMemory (frame + 0#64) _ query = _
    rw [StoreWord.put, if_neg notPC, byteAway query owned, sourceMemory]
  have pcView : MemoryExtend.View advanced frame base length capacity pointer scratch := by
    have memoryView := byteView.with_memory (StoreWord.put stored.memory (frame + 0#64) (pc + 1#64))
      (FrameField.put_other stored.memory frame 0#64 (pc + 1#64) 24#64 (by decide) |>.trans byteView.baseCell)
      (FrameField.put_other stored.memory frame 0#64 (pc + 1#64) 32#64 (by decide) |>.trans byteView.lengthCell)
      (FrameField.put_other stored.memory frame 0#64 (pc + 1#64) 40#64 (by decide) |>.trans byteView.capacityCell)
    exact memoryView.after_erase (by rw [advancedEq]; rfl)
  refine ⟨?_, result, ?_, pcView.after_erase (by rw [scopeEq, finalEq]; rfl), ?_, ?_, outside⟩
  · change 1 ≤ ready.clock at pcFits
    rw [readyClock] at pcFits
    omega
  · rw [scopeEq, finalEq]
    change advanced.clock = _
    rw [pcClock]
    change ready.clock - 1 = _
    rw [readyClock]
    omega
  · unfold regularBudget wordAt
    rw [outside _ (view.header_outside 64 (by decide)) (offsets_ne frame _ _ (by decide)),
      outside _ (view.header_outside 184 (by decide)) (offsets_ne frame _ _ (by decide)),
      outside _ (view.header_outside 192 (by decide)) (offsets_ne frame _ _ (by decide))]
  · exact outside _ (view.header_outside 184 (by decide)) (offsets_ne frame _ _ (by decide))

end InitECandidate.Solver.GasBudget.MemoryStore8

#print axioms InitECandidate.Solver.GasBudget.MemoryStore8.suffix_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryStore8.suffix_normal
