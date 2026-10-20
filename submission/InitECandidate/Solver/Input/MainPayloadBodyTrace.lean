import InitECandidate.Solver.Input.MainPayloadExtra
import InitECandidate.Solver.Input.MainPayloadNormal
import InitECandidate.Solver.Input.PayloadAfterExtraTrace

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Complete actual original payload body at main's reached entry, including
all offset/extra-data/transaction/withdrawal parser failures. All allocation,
code, mapping, slice and current-local premises derive from reached states. -/
theorem body_trace (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actual : DecoderCall.PayloadEntry input source entry)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (extent : 602 ≤ input.length % 2^64)
    (inside : 62+(length input).toNat≤input.length%2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Payload.afterGuard=(result,post)) (notTimeout : result≠some .timeOut) :
    entry.clock-post.clock≤(input.length%2^64)/4+76 ∧ source.clock-post.clock≤(input.length%2^64)/4+87 ∧
      ((∃ error : BitVec 64,(error=10#64 ∨ error=11#64 ∨ error=12#64 ∨ error=51#64 ∨ error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=30#64 ∨ error=31#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ result=some (.returned (.val (.word (cursor input))))) := by
  rcases extra_trace input source entry post environment actual bounded extent result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost,aggregate⟩ := rejected
    exact ⟨by omega,by omega,Or.inl ⟨error,by rcases allowed with rfl | rfl | rfl | rfl <;> simp,same⟩⟩
  obtain ⟨layout,extraBound,current,innerPost,reached,bodyForward,bodyLower,remaining,endpoint,preserved⟩ := normal
  have installed : OriginalCode.Installed current.code := reached.frame.code.symm ▸ environment.code
  have number := cursor_number input bounded
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432+input.length%2^64+8≤DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input≤2847949152 := geometry.2.1
  have small : input.length%2^64≤134217712 := bounded
  have cursorAfter : inputPointer.toNat+input.length%2^64+8≤(cursor input).toNat := by
    change 2713731432+input.length%2^64+8≤_; rw [number.1]; omega
  have cursorRoom : (cursor input).toNat+136+4*(input.length%2^64)≤33806089496 := by rw [number.1]; omega
  have arrayGeometry := Payload.payload_array_geometry input inputPointer (cursor input) number.2 cursorAfter cursorRoom
  obtain ⟨txLower,txOrdered,txInside⟩ := Payload.transaction_range input (length input) layout.valid inside
  have txLength : Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566≤input.length%2^64 := by omega
  have heap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded (cursor input) 136#64))) := by
    rw [reached.frame.globals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have extra : current.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)) := by simpa only [layout.first] using reached.extra
  obtain ⟨cost,outcome⟩ := Payload.after_extra_trace current innerPost input inputPointer (cursor input) (PersistentAlloc.rounded (cursor input) 136#64) (length input)
    reached.bytes extent reached.pointer reached.payload reached.length extra reached.transactions reached.withdrawals reached.balances layout.valid inside
    (reached.frame.domain.trans environment.domain) (by decide) number.2 arrayGeometry.2.1 (by decide) cursorAfter (by omega) arrayGeometry.2.2.1 (by have := arrayGeometry.2.2.2; omega) heap
    (PersistentAlloc.original_code current.code installed) (DecoderRuntime.division_code current.code installed) (DecoderCall.original_fail_code current.code installed)
    (by rw [reached.frame.exceptions]; exact environment.shapes .SszErr) (DecoderRuntime.var_list_code current.code installed) (DecoderRuntime.fixed_list_code current.code installed) result remaining notTimeout
  have postClock : post.clock=innerPost.clock := by
    rw [endpoint]
    have h := congrArg PanSemStateFiniteExact.clock (preserved innerPost)
    exact h
  have tailForward := evaluateHOLFiniteState_clock_le current Payload.afterExtra
  rw [remaining] at tailForward
  change innerPost.clock≤current.clock at tailForward
  have prefixCost := reached.frame.clockLower
  have prefixForward := reached.frame.forward
  refine ⟨by rw [postClock]; omega,by rw [postClock]; omega,?_⟩
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    exact Or.inl ⟨error,Or.inr (Or.inr (Or.inr (Or.inr allowed))),same⟩
  · exact Or.inr normal

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.body_trace
