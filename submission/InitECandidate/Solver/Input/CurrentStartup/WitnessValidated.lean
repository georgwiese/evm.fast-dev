import InitECandidate.Solver.Input.CurrentStartup.WitnessEntry
import InitECandidate.Solver.Input.CurrentStartup.CallerContextControl
import InitECandidate.Solver.Input.Witness.OffsetsTrace

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessValidated
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength
  heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) current
  wp : current.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2 + Guest.GasLimit.le32 input 6))))
  wlen : current.locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6))))
  minimum : 12 ≤ input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6
  first : Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 0 = 12#64
  valid : ∀ index < 3, Offsets.ValidAt 12#64 (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6))
    (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6)) index
  cells : ∀ index < 3, current.memory (WitnessRadix.byteAddress 2701132528#64 (8 * index)) =
    .word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) index)
  requestCell : current.memory (statelessRecord + 32#64) = .word requestRecord
  control : WitnessRadix.BackingLayout.control current = WitnessRadix.BackingLayout.control source
  price : source.clock - current.clock ≤ 8
  clock : current.clock ≤ source.clock
  returned : evaluateHOLFiniteState current Witness.loadedBody = (some (.returned value), post)
  endpoint : ∃ caller originalPost, WitnessEntry.Result input caller source originalPost
    pointer statelessRecord record gasWord requestRecord payloadLength value ∧
    LocalEffects.erase originalPost = LocalEffects.erase post ∧ originalPost.clock = post.clock

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength : Nat, ∃ value : ValueHOL 64,
      Result input source current post pointer statelessRecord record gasWord requestRecord payloadLength value

/-- The actual three workspace writes and validator derive all witness
slice offsets. Their low-address frame protects the earlier request/gas cells. -/
theorem entry (input : Guest.InputBlob) (actual : WitnessEntry.Reached input) : Reached input := by
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, value, data⟩ := actual
  have context := data.context
  have extent : 2 + Guest.GasLimit.le32 input 6 + 12 ≤ input.length % 2^64 := by
    have := context.request.outer.upper
    have := data.minimum
    omega
  have inputRoom : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 := by
    have := context.statelessLower
    have := context.statelessRoom
    omega
  rcases Witness.offsets_trace source post input pointer 2701132528#64
    (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6)) (2 + Guest.GasLimit.le32 input 6)
    context.image extent data.wp data.wlen context.workspace context.domain context.pointerAligned
    (by decide) (by decide) (by have := context.pointerLower; change 2701132528 + 24 ≤ pointer.toNat; omega)
    (by omega) (CanonicalHeader.offset_code source.code context.code) (CanonicalHeader.fail_code source.code context.code)
    (context.shapes .SszErr) (some (.returned value)) data.returned (by simp) with rejected | completed
  · obtain ⟨error, allowed, impossible, price⟩ := rejected
    cases impossible
  · obtain ⟨first, valid, current, inner, clock, price, control, image, locals, cells, remaining, restored, memory⟩ := completed
    have gasNumber : (record + 88#64).toNat = record.toNat + 88 := by
      rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; have := context.recordRoom; omega)]
      rfl
    have gas := (memory (record + 88#64) (Or.inr (by
      rw [gasNumber]; have := context.pointerLower; have := context.statelessLower; have := context.recordAfter
      change 2701132528 + 24 ≤ record.toNat + 88; omega))).trans context.gasCell
    have kept (name : String) (member : name ∈ ["pl", "si", "np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit"]) :
        current.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
      apply locals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have currentContext := PayloadCallerReturn.Context.of_control input source current pointer statelessRecord record gasWord
      payloadLength context control image gas kept
    have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
    have heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) current := by
      obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
      exact ⟨cursor, (congrArg (fun table => table.lookup (ofString "heap_ptr")) globals).trans cell, low, high, aligned⟩
    have siNumber : (statelessRecord + 32#64).toNat = statelessRecord.toNat + 32 := by
      rw [BitVec.toNat_add_of_lt (by change statelessRecord.toNat + 32 < 2^64; have := context.statelessRoom; omega)]
      rfl
    have requestCell := (memory (statelessRecord + 32#64) (Or.inr (by
      rw [siNumber]; have := context.pointerLower; have := context.statelessLower
      change 2701132528 + 24 ≤ statelessRecord.toNat + 32; omega))).trans data.requestCell
    refine ⟨source, current, inner, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, value,
      ⟨currentContext, heap, (locals (ofString "wp") (by decide)).trans data.wp,
        (locals (ofString "wlen") (by decide)).trans data.wlen, data.minimum, first, valid, cells,
        requestCell, control, price, clock, remaining, ⟨caller, post, data, ?_, ?_⟩⟩⟩
    · rw [restored]
      rfl
    · rw [restored]
      rfl

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  entry input (WitnessEntry.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessValidated

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessValidated.entry
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessValidated.separated
