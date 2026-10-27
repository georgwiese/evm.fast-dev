import InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Shared caller transport across a real allocating helper: immutable fields,
actual input/gas memory, bounded post-frontier and live locals stay explicit. -/
theorem Context.of_fields (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat)
    (context : Context input source pointer statelessRecord record gasWord length)
    (code : target.code = source.code) (shapes : target.eshapes = source.eshapes)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be)
    (workspace : target.globals.lookup (ofString "ssz_offs") = source.globals.lookup (ofString "ssz_offs"))
    (image : Blob.HeapInput target input pointer) (gas : target.memory (record + 88#64) = .word gasWord)
    (heap : NormalHeapEffects.AtLeast (record.toNat + 136) target)
    (kept : ∀ name ∈ ["pl", "si", "np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit"],
      target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) :
    Context input target pointer statelessRecord record gasWord length := by
  refine ⟨?_, ?_, domain.trans context.domain, endian.trans context.endian, image, heap,
    (kept "pl" (by simp)).trans context.pl, (kept "si" (by simp)).trans context.si,
    context.statelessLower, context.statelessAligned, context.statelessRoom, context.recordAfter, context.recordAligned,
    context.recordRoom, gas, context.gasBound, context.pointerLower, context.pointerAligned, context.inputBound, context.slice,
    ⟨(kept "np" (by simp)).trans context.request.np, (kept "nlen" (by simp)).trans context.request.nlen,
      (kept "o_vh" (by simp)).trans context.request.vh, (kept "o_rq" (by simp)).trans context.request.rq,
      context.request.valid, context.request.upper, context.request.outer.preserved ?_⟩, workspace.trans context.workspace⟩
  · rw [code]; exact context.code
  · rw [shapes]; exact context.shapes
  · intro name member
    apply kept
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.of_fields
