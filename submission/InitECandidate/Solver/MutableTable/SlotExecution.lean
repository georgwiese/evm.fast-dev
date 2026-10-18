import InitECandidate.Solver.MutableTable.SlotProgram
import InitECandidate.Solver.MutableTable.DeleteMoveReads

namespace InitECandidate.Solver.MutableTable.Slot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Full unchanged slot-reader body, all actual header/byte/value loads and
tuple return. It has no source clocks and preserves every nonlocal field. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (index : Nat) (inside : index < plan.capacity)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    ∃ value target, evaluateHOLFiniteState source body = (some (.returned (triple (if index ∈ slots then 1#64 else 0#64)
      (cell plan .keys 0 + BitVec.ofNat 64 index * BitVec.ofNat 64 (stride kind)) value)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite source := by
  classical
  let used : BitVec 64 := if index ∈ slots then 1#64 else 0#64
  let pointer := cell plan .keys 0 + BitVec.ofNat 64 index * BitVec.ofNat 64 (stride kind)
  let us := bind source "used" used
  let ks := bind us "keyp" pointer
  obtain ⟨value, valueCell⟩ : ∃ value, source.memory (cell plan .values (8 * index)) = .word value := by
    cases stored : source.memory (cell plan .values (8 * index)) with | word value => exact ⟨value, rfl⟩
  let vs := bind ks "val" value
  have readHeader (target : PanSemStateFiniteExact 64 Guest.HostMemory) (sameLocals : target.locals.lookup (ofString "t") = source.locals.lookup (ofString "t"))
      (sameMemory : target.memory = source.memory) (sameDomain : target.memaddrs = source.memaddrs)
      (offset : Nat) (range : offset < 72) (aligned : offset % 8 = 0) (word : BitVec 64)
      (member : (offset, word) ∈ MemoryModel.headerEntries kind plan (BitVec.ofNat 64 slots.length)) :
      eval target (Find.tableLoad (BitVec.ofNat 64 offset)) = some (.val (.word word)) :=
    MemoryModel.Header.read target kind plan valid (sameDomain.trans domain) _ (by rw [sameMemory]; exact header) (sameLocals.trans tableLocal) offset range aligned word member
  have usedHeader := readHeader source rfl rfl rfl 48 (by decide) (by decide) (cell plan .used 0) (by simp [MemoryModel.headerEntries])
  have actualUsed := occupied.used index inside
  have usedRead : eval source usedExpression = some (.val (.word used)) := by
    simp only [eval] at usedHeader
    change @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be (cell plan .used 0 + BitVec.ofNat 64 index) = some (if index ∈ slots then 1 else 0) at actualUsed
    by_cases member : index ∈ slots <;> simp [eval, usedExpression, localVar, evalHOLExact, evalListHOLExact, toExact, usedHeader, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp, actualUsed, used, member]
  have usT : us.locals.lookup (ofString "t") = source.locals.lookup (ofString "t") := bind_lookup_other _ "used" "t" _ (by decide)
  have usI : us.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := (bind_lookup_other _ "used" "i" _ (by decide)).trans indexLocal
  have keysHeader := readHeader us usT rfl rfl 32 (by decide) (by decide) (cell plan .keys 0) (by simp [MemoryModel.headerEntries])
  have strideHeader := readHeader us usT rfl rfl 8 (by decide) (by decide) (BitVec.ofNat 64 (stride kind)) (by simp [MemoryModel.headerEntries])
  have keyRead : eval us keyExpression = some (.val (.word pointer)) := by
    simp only [eval] at keysHeader strideHeader
    simp [eval, keyExpression, localVar, evalHOLExact, evalListHOLExact, toExact, keysHeader, strideHeader, usI, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, pointer]
  have ksT : ks.locals.lookup (ofString "t") = source.locals.lookup (ofString "t") := (bind_lookup_other _ "keyp" "t" _ (by decide)).trans usT
  have ksI : ks.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))) := (bind_lookup_other _ "keyp" "i" _ (by decide)).trans usI
  have valsHeader := readHeader ks ksT rfl rfl 40 (by decide) (by decide) (cell plan .values 0) (by simp [MemoryModel.headerEntries])
  have valueMapped : ks.memaddrs (cell plan .values 0 + BitVec.ofNat 64 index * 8#64) := by
    rw [Delete.Move.natural_word_address kind plan valid .values index inside]
    change source.memaddrs _
    rw [domain]
    exact mapped kind plan valid .values _ (by change 8 * index < 8 * plan.capacity; omega) (by omega)
  have valueStored : ks.memory (cell plan .values 0 + BitVec.ofNat 64 index * 8#64) = .word value := by
    rw [Delete.Move.natural_word_address kind plan valid .values index inside]
    exact valueCell
  have valueRead : eval ks valueExpression = some (.val (.word value)) := by
    simp only [eval] at valsHeader
    simp [eval, valueExpression, localVar, evalHOLExact, evalListHOLExact, toExact, valsHeader, ksI, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      memLoadHOLExact, isWfShapeExactHOL, valueMapped, valueStored]
  have vUsed : vs.locals.lookup (ofString "used") = some (.val (.word used)) := (bind_lookup_other _ "val" "used" _ (by decide)).trans ((bind_lookup_other _ "keyp" "used" _ (by decide)).trans (bind_lookup_same _ _ _))
  have vKey : vs.locals.lookup (ofString "keyp") = some (.val (.word pointer)) := (bind_lookup_other _ "val" "keyp" _ (by decide)).trans (bind_lookup_same _ _ _)
  have vVal : vs.locals.lookup (ofString "val") = some (.val (.word value)) := bind_lookup_same _ _ _
  have returned : evaluateHOLFiniteState vs afterValue = (some (.returned (triple used pointer value)), emptyLocalsHOLFinite vs) := by
    simp [afterValue, evaluateHOLFiniteState_return, localVar, evalHOLExact, evalListHOLExact, toExact, vUsed, vKey, vVal, triple, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have valRun := Input.ScalarScope.declare_execute ks _ "val" valueExpression value afterValue _ valueRead returned
  have keyRun := Input.ScalarScope.declare_execute us _ "keyp" keyExpression pointer (.dec (ofString "val") .one valueExpression afterValue) _ keyRead valRun
  have usedRun := Input.ScalarScope.declare_execute source _ "used" usedExpression used (.dec (ofString "keyp") .one keyExpression (.dec (ofString "val") .one valueExpression afterValue)) _ usedRead keyRun
  let target := restore source "used" (restore us "keyp" (restore ks "val" (emptyLocalsHOLFinite vs)))
  refine ⟨value, target, ?_, rfl⟩
  rw [body_shape]
  exact usedRun

end InitECandidate.Solver.MutableTable.Slot

#print axioms InitECandidate.Solver.MutableTable.Slot.execute
