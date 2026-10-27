import InitECandidate.Solver.Input.CurrentStartup.RequestsEntry
import InitECandidate.Solver.Input.Requests.OffsetsTrace

namespace InitECandidate.Solver.Input.CurrentStartup.RequestsValidated
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (payloadLength start size : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input caller pointer statelessRecord record gasWord payloadLength
  code : OriginalCode.Installed current.code
  shapes : OriginalExceptions.Installed current.eshapes
  domain : current.memaddrs = InitE.ordinaryDomain
  endian : current.be = false
  image : Blob.HeapInput current input pointer
  heap : NormalHeapEffects.AtLeast (record.toNat + 136) current
  workspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))
  p : current.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start)))
  len : current.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 size)))
  inside : start + size ≤ input.length % 2^64
  minimum : 20 ≤ size
  first : Requests.offsetWord input start 0 = 20#64
  valid : ∀ position < 5, Offsets.ValidAt 20#64 (BitVec.ofNat 64 size) (Requests.offsetWord input start) position
  cells : ∀ position < 5, current.memory (WitnessRadix.byteAddress 2701132528#64 (8 * position)) = .word (Requests.offsetWord input start position)
  gasCell : current.memory (record + 88#64) = .word gasWord
  returned : evaluateHOLFiniteState current Requests.afterOffsets = (some (.returned value), post)
  endpoint : ∃ entry originalPost, RequestsEntry.Result (decoderOrigin := decoderOrigin) input caller entry originalPost pointer statelessRecord record gasWord payloadLength start size value ∧
    WitnessRadix.BackingLayout.control current = WitnessRadix.BackingLayout.control entry ∧
    current.clock ≤ entry.clock ∧ entry.clock - current.clock ≤ 12 ∧ LocalEffects.erase originalPost = LocalEffects.erase post ∧ originalPost.clock = post.clock

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller current post, ∃ pointer statelessRecord record gasWord : BitVec 64, ∃ payloadLength start size : Nat, ∃ value : ValueHOL 64,
    Result (decoderOrigin := decoderOrigin) input caller current post pointer statelessRecord record gasWord payloadLength start size value

/-- The actual five-offset validator derives its real first offset and all
range/order guards. Its earlier workspace writes preserve the payload gas cell. -/
theorem entry (input : Guest.InputBlob) (actual : RequestsEntry.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  obtain ⟨caller, source, post, pointer, statelessRecord, record, gasWord, payloadLength, start, size, value, data⟩ := actual
  have context := data.context
  have sourceWorkspace : source.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by
    obtain ⟨callee, parentPost, parentValue, entryEq, args, called, run⟩ := data.invocation
    rw [entryEq]
    exact context.workspace
  have pointerRoom : pointer.toNat + input.length % 2^64 + 8 ≤ 2952790016 := by
    have := context.statelessLower
    have := context.statelessRoom
    omega
  rcases Requests.offsets_trace source post input pointer 2701132528#64 (BitVec.ofNat 64 size) start data.image
    (by have := data.inside; have := data.minimum; omega) data.p data.len sourceWorkspace data.domain context.pointerAligned
    (by decide) (by decide) (by have := context.pointerLower; change 2701132528 + 40 ≤ pointer.toNat; omega) (by omega)
    (CanonicalHeader.offset_code source.code data.code) (CanonicalHeader.fail_code source.code data.code) (data.shapes .SszErr)
    (some (.returned value)) data.returned (by simp) with rejected | continued
  · obtain ⟨error, allowed, impossible, price⟩ := rejected
    cases impossible
  · obtain ⟨first, valid, current, innerPost, forward, price, control, image, locals, cells, remaining, restored, memory⟩ := continued
    have globals : current.globals = source.globals := by
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
      exact same
    have code : current.code = source.code := by
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.code) control
      exact same
    have shapes : current.eshapes = source.eshapes := by
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.eshapes) control
      exact same
    have domain : current.memaddrs = source.memaddrs := by
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
      exact same
    have endian : current.be = source.be := by
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) control
      exact same
    have heap : NormalHeapEffects.AtLeast (record.toNat + 136) current := by
      obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
      exact ⟨cursor, (congrArg (fun table => table.lookup (ofString "heap_ptr")) globals).trans cell, low, high, aligned⟩
    have gasNat : (record + 88#64).toNat = record.toNat + 88 := by
      rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; have := context.recordRoom; omega)]
      rfl
    have gasFrame := memory (record + 88#64) (Or.inr (by
      rw [gasNat]
      change 2701132528 + 40 ≤ record.toNat + 88
      have := context.recordAfter
      have := context.statelessLower
      have := context.pointerLower
      omega))
    have sourceGas : source.memory (record + 88#64) = .word gasWord := by
      obtain ⟨callee, parentPost, parentValue, entryEq, args, called, run⟩ := data.invocation
      rw [entryEq]
      exact context.gasCell
    have currentWorkspace : current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64)) := by
      rw [globals]
      obtain ⟨callee, parentPost, parentValue, entryEq, args, called, run⟩ := data.invocation
      rw [entryEq]
      exact context.workspace
    exact ⟨caller, current, innerPost, pointer, statelessRecord, record, gasWord, payloadLength, start, size, value,
      ⟨context, code ▸ data.code, shapes ▸ data.shapes, domain.trans data.domain, endian.trans data.endian, image, heap,
        currentWorkspace, (locals (ofString "p") (by decide)).trans data.p, (locals (ofString "len") (by decide)).trans data.len,
        data.inside, data.minimum, first, valid, cells, gasFrame.trans sourceGas, remaining,
        source, post, data, control, forward, price, by rw [restored]; rfl, by rw [restored]; rfl⟩⟩

theorem separated (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached (decoderOrigin := decoderOrigin) input :=
  entry input (RequestsEntry.separated input actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestsValidated

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsValidated.entry
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsValidated.separated
