import InitECandidate.Solver.Input.MainDecoderOuterFields
import InitECandidate.Solver.Input.RequestSetupTrace

namespace InitECandidate.Solver.Input.Main.RequestPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def cursor (input : Guest.InputBlob) : BitVec 64 := BitVec.ofNat 64 (DecoderSetup.cursor input + 288)
def current (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :=
  {DecoderCall.outerState source input with clock := clock}
def ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (clock : Nat) :=
  Request.prepared (current source input clock) input inputPointer (cursor input) (Guest.GasLimit.le32 input 6)

/-- Instantiate the actual request allocation/store/declaration prefix using
main's current heap, initialized workspace, copied bytes and real offsets.
The enclosing non-timeout execution supplies its actual allocation tick. -/
theorem setup_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (clock : Nat)
    (environment : DecoderCall.Environment input source) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (extent : 18 ≤ input.length % 2^64) (first : Guest.GasLimit.le32 input 2 = 16) (witnessLower : 16 ≤ Guest.GasLimit.le32 input 6)
    (heap : Blob.HeapInput (current source input clock) input inputPointer)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (current source input clock) Header.continuation = (result,post)) (notTimeout : result ≠ some .timeOut) :
    1 ≤ clock ∧ ∃ restoreStack innerPost,
      ProgramPrefix.Executes (current source input clock) Request.actions (ready source input clock) restoreStack ∧
      Blob.HeapInput (ready source input clock) input inputPointer ∧
      evaluateHOLFiniteState (ready source input clock) (.seq Request.lengthGuard Request.requestBody) = (result,innerPost) ∧ post = restoreStack innerPost := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2
  have number : (cursor input).toNat = DecoderSetup.cursor input + 288 := by
    rw [cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have globals : (current source input clock).globals = source.globals := DecoderCall.outer_globals source input
  have cells := DecoderCall.outer_cells source input first
  have p := (DecoderCall.outer_bindings source input).1
  have firstMapped : (current source input clock).memaddrs 2713715344#64 := by
    change source.memaddrs 2713715344#64
    rw [environment.domain]
    exact BackingLayout.ordinary_mapped _ (by decide) (by decide) (by decide)
  have secondMapped : (current source input clock).memaddrs 2713715352#64 := by
    change source.memaddrs 2713715352#64
    rw [environment.domain]
    exact BackingLayout.ordinary_mapped _ (by decide) (by decide) (by decide)
  have offsets : (current source input clock).globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by rw [globals]; exact environment.offsets
  have heapGlobal : (current source input clock).globals.lookup (ofString "heap_ptr") = some (.val (.word (cursor input))) := by rw [globals]; exact environment.heap
  exact Request.setup_trace (current source input clock) post input inputPointer 2713715344#64 (cursor input) (Guest.GasLimit.le32 input 6) witnessLower heap extent p offsets firstMapped secondMapped cells.1 cells.2 environment.domain (by decide)
    (by rw [number]; omega) (by decide) (by rw [number]; change 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input + 288; omega)
    (by rw [number]; omega) heapGlobal (PersistentAlloc.original_code source.code environment.code) result run notTimeout

end InitECandidate.Solver.Input.Main.RequestPrefix

#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.setup_trace
