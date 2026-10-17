import InitECandidate.Solver.WitnessRadix.Copy32Memory
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual ignored-result memcpy call restores caller locals and pays
one call clock and one loop clock. -/
theorem call_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (arguments : List (ExpHOL 64))
    (src dst : BitVec 64) (words : Fin 4 → BitVec 64)
    (argumentValues : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word dst), .val (.word src), .val (.word 32#64)])
    (code : lookupCodeHOLFinite source.code.lookup (ofString "memcpy")
      [.val (.word dst), .val (.word src), .val (.word 32#64)] = some (body, callee, .one))
    (srcLocal : callee.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : callee.lookup (ofString "dst") = some (.val (.word dst)))
    (lengthLocal : callee.lookup (ofString "n") = some (.val (.word 32#64)))
    (mask : (dst ||| src) &&& 7#64 = 0#64) (view : MemoryBytes.WordView source src words)
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + BitVec.ofNat 64 (8 * limb.val)))
    (separate : ∀ read write : Fin 4, src + BitVec.ofNat 64 (8 * read.val) ≠ dst + BitVec.ofNat 64 (8 * write.val))
    (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memcpy") arguments) =
      (none, { source with memory := memory source.memory dst words, clock := source.clock - 2 }) := by
  classical
  let entry := callEntryStateHOLFinite source callee
  have view' : MemoryBytes.WordView entry src words := ⟨view.mapped, view.stored⟩
  obtain ⟨target, run, frame⟩ := execute entry src dst words srcLocal dstLocal lengthLocal mask
    view' mapped separate (by change 1 ≤ source.clock - 1; omega)
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "memcpy")
    arguments [.val (.word dst), .val (.word src), .val (.word 32#64)] body callee .one
    (.val (.word 0#64)) target argumentValues code (by omega) run (by simp [shapeEqHOL, shapeOfHOLExact])
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with locals := source.locals }) frame
  have clockEq : source.clock - 1 - 1 = source.clock - 2 := by omega
  simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, clockEq] using callRun.trans
    (congrArg (fun state : PanSemStateFiniteExact 64 F => (none, state)) restored)

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.call_execute
