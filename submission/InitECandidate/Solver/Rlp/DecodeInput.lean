import InitECandidate.Solver.Rlp.DecodeNormalFrame
import InitECandidate.Solver.Rlp.DecodeGlobals
import InitECandidate.Solver.Rlp.ScratchBytes

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual full decode retains the copied input and persistent heap cursor
when the current scratch cursor lies below the real copied allocation. The
input extent remains length modulo2^64; no reached helper model is supplied. -/
theorem body_normal_input (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (inputBase pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (copied : Input.Blob.HeapInput source input inputBase) (aligned : inputBase.toNat%8=0)
    (inputFits : inputBase.toNat+input.length%2^64<2^64) (below : cursor.toNat≤inputBase.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    Complete pointer length value ∧ Validation.Arena post cursor limit ∧ Input.Blob.HeapInput post input inputBase ∧
      post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧ source.clock-post.clock≤60*length.toNat+43 := by
  obtain ⟨complete,nextArena,above,priced⟩ := body_normal_above source post pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  have fields := Input.evaluation_fields source post body (some (.returned value)) normal
  have copiedAfter := Input.Blob.HeapInput.above source post input inputBase inputBase.toNat copied
    (Validation.Above.mono source post cursor.toNat inputBase.toNat above below) aligned (Nat.le_refl _) inputFits fields.1 fields.2.1
  have heapFrame := globals (ofString "heap_ptr") source.code installed (by decide) source rfl
  rw [normal] at heapFrame
  have heapEq := congrArg Prod.snd heapFrame
  exact ⟨complete,nextArena,copiedAfter,heapEq,priced⟩

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Decode.body_normal_input
