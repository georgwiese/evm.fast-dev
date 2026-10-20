import InitECandidate.Solver.Input.MainDecoderPayloadCall
import InitECandidate.Solver.Input.PayloadPrefixTrace

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def cursor (input : Guest.InputBlob) := PersistentAlloc.rounded (RequestPrefix.cursor input) 96#64
def length (input : Guest.InputBlob) : BitVec 64 := BitVec.ofNat 64 (Guest.GasLimit.le32 input 22 - 44)
def ready (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) := Payload.prepared entry input inputPointer (cursor input) (length input)

theorem cursor_number (input : Guest.InputBlob) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) :
    (cursor input).toNat = DecoderSetup.cursor input + 384 ∧ (cursor input).toNat % 8 = 0 := by
  have geometry := input_cursor_bounds input bounded
  have small : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2
  have siNumber : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by
    rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have rounded := PersistentAlloc.rounded_nat (RequestPrefix.cursor input) 96#64 (by change (RequestPrefix.cursor input).toNat + 96 + 7 < 2^64; rw [siNumber]; omega)
  change (cursor input).toNat = ((RequestPrefix.cursor input).toNat + 96 + 7) / 8 * 8 at rounded
  rw [siNumber] at rounded
  exact ⟨by omega,by omega⟩

/-- Instantiate the actual payload136 allocation, both header stores and all
four raw offset declarations from the reached original payload entry. Its
clock is forced by the actual non-timeout body, and all bytes survive. -/
theorem setup_trace (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actual : DecoderCall.PayloadEntry input source entry)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (extent : 602 ≤ input.length % 2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Payload.afterGuard = (result,post)) (notTimeout : result ≠ some .timeOut) :
    1 ≤ entry.clock ∧ ∃ innerPost,
      ProgramPrefix.Executes entry Payload.prefixActions (ready entry input) (Payload.restorePrefix entry input inputPointer (cursor input) (length input)) ∧
      Blob.HeapInput (ready entry input) input inputPointer ∧
      evaluateHOLFiniteState (ready entry input) Payload.offsetBody = (result,innerPost) ∧ post = Payload.restorePrefix entry input inputPointer (cursor input) (length input) innerPost := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have number := cursor_number input bounded
  have heapGlobal : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (cursor input))) := by
    rw [actual.frame.globals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,cursor]
  have installed : OriginalCode.Installed entry.code := actual.frame.code.symm ▸ environment.code
  exact Payload.prefix_setup_trace entry post input inputPointer (cursor input) (length input) actual.bytes extent actual.pointer actual.length
    (actual.frame.domain.trans environment.domain) (by decide) number.2 (by decide)
    (by rw [number.1]; change 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input + 384; omega)
    (by rw [number.1]; omega) heapGlobal (PersistentAlloc.original_code entry.code installed) result run notTimeout

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.cursor_number
#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.setup_trace
