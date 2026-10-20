import InitECandidate.Solver.Input.MainRequestFields

namespace InitECandidate.Solver.Input.Main.RequestPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Saved original outer-container locals needed after payload/request calls
resume, including the real witness offset. All are actual prefix bindings. -/
theorem ready_roots (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :
    (ready source input clock).locals.lookup (ofString "p") = some (.val (.word (inputPointer + 2#64))) ∧
    (ready source input clock).locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) ∧
    (ready source input clock).locals.lookup (ofString "o_wit") = some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6)))) := by
  let root := current source input clock
  let witness := Guest.GasLimit.le32 input 6
  have initial := DecoderCall.outer_bindings source input
  have chained := Request.chained_locals root input inputPointer (cursor input) witness initial.1
  have loadedLength : (Request.loaded root witness).locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) :=
    (bind_lookup_other (QueryBranch.bind root "o_npr" 16#64) "o_wit" "len" _ (by decide)).trans
      ((bind_lookup_other root "o_npr" "len" _ (by decide)).trans initial.2)
  have chainedLength : (Request.chained root input (cursor input) witness).locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) :=
    (bind_lookup_other (PersistentAlloc.post {Request.loaded root witness with clock := root.clock - 1} (cursor input) 96#64) "si" "len" _ (by decide)).trans loadedLength
  refine ⟨?_,?_,?_⟩
  · exact (bind_lookup_other (Request.positioned root input inputPointer (cursor input) witness) "nlen" "p" _ (by decide)).trans
      ((bind_lookup_other (Request.chained root input (cursor input) witness) "np" "p" _ (by decide)).trans chained.1)
  · exact (bind_lookup_other (Request.positioned root input inputPointer (cursor input) witness) "nlen" "len" _ (by decide)).trans
      ((bind_lookup_other (Request.chained root input (cursor input) witness) "np" "len" _ (by decide)).trans chainedLength)
  · exact (bind_lookup_other (Request.positioned root input inputPointer (cursor input) witness) "nlen" "o_wit" _ (by decide)).trans
      ((bind_lookup_other (Request.chained root input (cursor input) witness) "np" "o_wit" _ (by decide)).trans chained.2.2)

end InitECandidate.Solver.Input.Main.RequestPrefix

#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.ready_roots
