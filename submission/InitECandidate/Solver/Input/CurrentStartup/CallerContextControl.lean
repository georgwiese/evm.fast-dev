import InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
import InitECandidate.Solver.PanControl

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Transport the shared decoder context across an exact control frame.
Actual input/gas memory and the nine live locals are supplied separately. -/
theorem Context.of_control (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord : BitVec 64) (length : Nat)
    (context : Context input source pointer statelessRecord record gasWord length)
    (control : WitnessRadix.BackingLayout.control target = WitnessRadix.BackingLayout.control source)
    (image : Blob.HeapInput target input pointer) (gas : target.memory (record + 88#64) = .word gasWord)
    (kept : ∀ name ∈ ["pl", "si", "np", "nlen", "o_vh", "o_rq", "p", "len", "o_wit"],
      target.locals.lookup (ofString name) = source.locals.lookup (ofString name)) :
    Context input target pointer statelessRecord record gasWord length := by
  have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with locals := target.locals, memory := target.memory, clock := target.clock}) control
  change target = {source with locals := target.locals, memory := target.memory, clock := target.clock} at same
  rw [same] at image gas kept ⊢
  refine ⟨context.code, context.shapes, context.domain, context.endian, image, context.heap,
    (kept "pl" (by simp)).trans context.pl, (kept "si" (by simp)).trans context.si,
    context.statelessLower, context.statelessAligned, context.statelessRoom, context.recordAfter, context.recordAligned,
    context.recordRoom, gas, context.gasBound, context.pointerLower, context.pointerAligned, context.inputBound, context.slice,
    ⟨(kept "np" (by simp)).trans context.request.np, (kept "nlen" (by simp)).trans context.request.nlen,
      (kept "o_vh" (by simp)).trans context.request.vh, (kept "o_rq" (by simp)).trans context.request.rq,
      context.request.valid, context.request.upper, context.request.outer.preserved ?_⟩, context.workspace⟩
  intro name member
  apply kept
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp

end InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadCallerReturn.Context.of_control
