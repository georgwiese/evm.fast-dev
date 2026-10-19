import InitECandidate.Solver.GasBudget.AddressMaskedProgram

namespace InitECandidate.Solver.GasBudget.AddressMasked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite MemoryWriter

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem stores_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : U256Value.Words)
    (installed : Input.OriginalCode.Installed source.code)
    (pointerLocal : source.locals.lookup (ofString "a") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "v") = some (U256Value.tuple words))
    (mapped : BytesMapped source pointer 20)
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source stores = (some (.returned returned), post)) :
    returned = .val (.word pointer) ∧ ∃ paid, paid ≤ 7 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase {source with memory := post.memory} ∧
      (∀ query, BytesAway pointer query 20 → post.memory query = source.memory query) := by
  have firstSafe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "st_be32") (arguments 0 2)) := .call none _ _ (by simp)
  obtain ⟨first, firstRun, secondRun, saved⟩ := firstSafe.normal_continue source post second returned run
  have firstArgs := arguments_read source pointer words 0 2 pointerLocal valueLocal
  simp only [BitVec.add_zero] at firstArgs
  have firstMapped : BytesMapped source pointer 4 := by simpa using mapped.subrange 0 4 (by decide)
  obtain ⟨firstFits, firstEq⟩ := Be32Stores.call_normal source first pointer (words 2) (arguments 0 2) installed firstArgs (be32_mapped firstMapped) firstRun
  have firstCanonical : first = {source with memory := first.memory, clock := source.clock - 1} := by rw [firstEq]
  have firstClock : first.clock = source.clock - 1 := by rw [firstEq]
  have firstAway (query : BitVec 64) (away : BytesAway pointer query 20) : first.memory query = source.memory query := by
    rw [firstEq]
    exact Be32Stores.written_away _ _ _ _ _ _ (be32_away (by simpa using away.subrange 0 4 (by decide)))
  have secondSafe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "st_be64") (arguments 4 1)) := .call none _ _ (by simp)
  obtain ⟨middle, secondCall, thirdRun, savedSecond⟩ := secondSafe.normal_continue first post third returned secondRun
  have firstInstalled : Input.OriginalCode.Installed first.code := by rw [firstCanonical]; exact installed
  have firstPointer : first.locals.lookup (ofString "a") = some (.val (.word pointer)) := by rw [firstCanonical]; exact pointerLocal
  have firstValue : first.locals.lookup (ofString "v") = some (U256Value.tuple words) := by rw [firstCanonical]; exact valueLocal
  have secondMapped : BytesMapped first (pointer + 4#64) 8 := by rw [firstCanonical]; exact mapped.subrange 4 8 (by decide)
  obtain ⟨paidSecond, secondBound, secondFits, secondClock, secondCanonical, secondAway⟩ :=
    be64_call_normal first middle (pointer + 4#64) (words 1) firstInstalled (arguments 4 1)
      (arguments_read first pointer words 4 1 firstPointer firstValue) secondMapped secondCall
  have thirdSafe : Input.LocalPrefix (ofString "setup") (.call (some (none, none)) (ofString "st_be64") (arguments 12 0)) := .call none _ _ (by simp)
  obtain ⟨last, thirdCall, returnRun, savedThird⟩ := thirdSafe.normal_continue middle post (.return (localVar "a")) returned thirdRun
  have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [secondCanonical]; exact firstInstalled
  have middlePointer : middle.locals.lookup (ofString "a") = some (.val (.word pointer)) := by rw [secondCanonical]; exact firstPointer
  have middleValue : middle.locals.lookup (ofString "v") = some (U256Value.tuple words) := by rw [secondCanonical]; exact firstValue
  have thirdMapped : BytesMapped middle (pointer + 12#64) 8 := by rw [secondCanonical, firstCanonical]; exact mapped.subrange 12 8 (by decide)
  obtain ⟨paidThird, thirdBound, thirdFits, thirdClock, thirdCanonical, thirdAway⟩ :=
    be64_call_normal middle last (pointer + 12#64) (words 0) middleInstalled (arguments 12 0)
      (arguments_read middle pointer words 12 0 middlePointer middleValue) thirdMapped thirdCall
  have lastPointer : last.locals.lookup (ofString "a") = some (.val (.word pointer)) := by rw [thirdCanonical]; exact middlePointer
  have read : eval last (localVar "a") = some (.val (.word pointer)) := by simp [eval, localVar, evalHOLExact, toExact, lastPointer]
  obtain ⟨actualRead, postEq⟩ := Input.return_normal last post (localVar "a") returned returnRun
  refine ⟨Option.some.inj (actualRead.symm.trans read), 1 + paidSecond + paidThird, by omega, ?_, ?_, ?_, ?_⟩
  · rw [secondClock, firstClock] at thirdFits
    rw [firstClock] at secondFits
    omega
  · rw [postEq]
    change last.clock = _
    rw [thirdClock, secondClock, firstClock]
    omega
  · rw [postEq, thirdCanonical, secondCanonical, firstCanonical]
    rfl
  · intro query away
    rw [postEq]
    exact (thirdAway query (away.subrange 12 8 (by decide))).trans
      ((secondAway query (away.subrange 4 8 (by decide))).trans (firstAway query away))

end InitECandidate.Solver.GasBudget.AddressMasked

#print axioms InitECandidate.Solver.GasBudget.AddressMasked.stores_normal
