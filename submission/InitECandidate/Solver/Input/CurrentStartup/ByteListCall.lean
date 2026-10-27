import InitECandidate.Solver.Input.CurrentStartup.ByteListData
import InitECandidate.Solver.Input.CurrentStartup.CallerContextFields
import InitECandidate.Solver.Input.BytesList.OriginalCode
import InitECandidate.Solver.Input.BytesList.Environment

namespace InitECandidate.Solver.Input.CurrentStartup.ByteListCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Reusable actual byte-list caller return. The real returned allocation
protects every earlier word and the physical payload gas; caller scopes remain
live for the unchanged continuation. No minimum clock or future room is assumed. -/
theorem normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord limit maximum : BitVec 64) (payloadLength start length floor : Nat)
    (context : PayloadCallerReturn.Context input source pointer statelessRecord record gasWord payloadLength)
    (heap : NormalHeapEffects.AtLeast floor source)
    (afterRecord : record.toNat + 136 ≤ floor)
    (inside : start + length ≤ input.length % 2^64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (fresh : ofString name ∉ [ofString "pl", ofString "si", ofString "np", ofString "nlen", ofString "o_vh", ofString "o_rq",
      ofString "p", ofString "len", ofString "o_wit"])
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (BytesList.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum))
    (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (.decCall (ofString name) VarList.returnShape
      (ofString "decode_bytes_list") arguments continuation) = (some (.returned value), post)) :
    ∃ current inner array,
      PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength ∧
      NormalHeapEffects.AtLeast floor current ∧
      NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start length) current ∧
      current.locals = source.locals.update (ofString name,
        BytesList.pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)) ∧
      VarList.Records current input pointer array start length ∧
      VarList.decodedCount input start length ≤ limit.toNat ∧
      (∀ index < VarList.decodedCount input start length,
        (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat ≤ maximum.toNat) ∧
      (∀ query : BitVec 64, query.toNat < array.toNat → current.memory query = source.memory query) ∧
      floor ≤ array.toNat ∧ array.toNat % 8 = 0 ∧ array.toNat ≤ 2952790016 ∧
      current.clock ≤ source.clock ∧ source.clock - current.clock ≤ 2*(length/4)+3 ∧
      evaluateHOLFiniteState current continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  classical
  obtain ⟨callee, called, p, n, l, m⟩ := BytesList.environment source.code.lookup
    (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit maximum (BytesList.original_code source.code context.code)
  have positive := CallNormal.normal_clock source post (ofString name) VarList.returnShape
    (ofString "decode_bytes_list") arguments continuation value actual
  obtain ⟨bodyPost, returned, bodyRun⟩ := CallNormal.callee_return source post (ofString name) VarList.returnShape
    (ofString "decode_bytes_list") arguments _ BytesList.body continuation callee VarList.returnShape args called positive value actual
  let entry := callEntryStateHOLFinite source callee
  have afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ floor := by
    have := context.statelessLower
    have := context.recordAfter
    omega
  obtain ⟨array, data⟩ := ByteListData.normal input entry bodyPost pointer limit maximum start length floor context.code
    context.shapes context.domain heap afterInput context.image inside (by have := context.pointerLower; omega)
    context.pointerAligned context.inputBound p n l m returned bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) VarList.returnShape &&
      shapeEqHOL (shapeOfHOLExact returned) VarList.returnShape) = true := by
    rw [data.tuple]
    simp [BytesList.pairValue, VarList.pairValue, VarList.returnShape, shapeOfHOLExact, shapeEqHOL_eq_true]
  have invoked := CallNormal.return_execute source bodyPost name VarList.returnShape (ofString "decode_bytes_list") arguments _
    BytesList.body continuation callee VarList.returnShape returned args called positive bodyRun shapePass
  have resumed := invoked.symm.trans actual
  let current := CallNormal.continuationEntry source bodyPost name returned
  let inner := (evaluateHOLFiniteState current continuation).2
  have observed : (evaluateHOLFiniteState current continuation).1 = some (.returned value) := congrArg Prod.fst resumed
  have endpoint : post = restore source name inner := (congrArg Prod.snd resumed).symm
  have fields := evaluation_fields entry bodyPost BytesList.body (some (.returned returned)) bodyRun
  have workspace : current.globals.lookup (ofString "ssz_offs") = source.globals.lookup (ofString "ssz_offs") := by
    change bodyPost.globals.lookup (ofString "ssz_offs") = _
    have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) data.control
    by_cases empty : length = 0
    · simp only [if_pos empty] at globals
      exact congrArg (fun table => table.lookup (ofString "ssz_offs")) globals
    · simp only [if_neg empty] at globals
      change bodyPost.globals = (WitnessRadix.PersistentAlloc.post entry array
        (BitVec.ofNat 64 (16 * (Guest.GasLimit.le32 input start / 4)))).globals at globals
      rw [globals]
      simp [WitnessRadix.PersistentAlloc.post, HolFiniteMapExact.update, FUPDATE,
        show ofString "heap_ptr" ≠ ofString "ssz_offs" from by decide]
      rfl
  have kept (key : String) (member : key ∈ ["pl", "si", "np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit"]) :
      current.locals.lookup (ofString key) = source.locals.lookup (ofString key) := by
    have different : ofString name ≠ ofString key := by
      intro same
      apply fresh
      rw [same]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    change (source.locals.update (ofString name, returned)).lookup (ofString key) = _
    simp [HolFiniteMapExact.update, FUPDATE, different]
  have gasNumber : (record + 88#64).toNat = record.toNat + 88 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; have := context.recordRoom; omega)]
    rfl
  have gas := (data.memory (record + 88#64) (by rw [gasNumber]; have := data.arrayLower; omega)).trans context.gasCell
  have currentHeap : NormalHeapEffects.AtLeast (record.toNat + 136) current := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
    exact ⟨cursor, cell, by omega, high, aligned⟩
  have currentContext := PayloadCallerReturn.Context.of_fields input source current pointer statelessRecord record gasWord payloadLength
    context fields.2.2.2 fields.2.2.1 fields.1 fields.2.1 workspace data.image gas currentHeap kept
  refine ⟨current, inner, array, currentContext, data.heap, data.heapExtent, ?_,
    VarList.Records.of_memory bodyPost current input pointer array start length rfl data.records,
    data.countLimit, data.lengths, data.memory, data.arrayLower, data.arrayAligned, data.arrayBound, ?_, ?_, Prod.ext observed rfl, endpoint⟩
  · change source.locals.update (ofString name, returned) = _
    rw [data.tuple]
  · change bodyPost.clock ≤ source.clock
    have forward := data.clock
    change bodyPost.clock ≤ source.clock - 1 at forward
    omega
  · change source.clock - bodyPost.clock ≤ _
    have priced := data.price
    have forward := data.clock
    change source.clock - 1 - bodyPost.clock ≤ _ at priced
    change bodyPost.clock ≤ source.clock - 1 at forward
    omega

end InitECandidate.Solver.Input.CurrentStartup.ByteListCall

#print axioms InitECandidate.Solver.Input.CurrentStartup.ByteListCall.normal
