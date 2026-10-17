import InitECandidate.Solver.MutableTable.HashSizedCall
import InitECandidate.Solver.MutableTable.MemeqSizedMapped

namespace InitECandidate.Solver.MutableTable.HashSized
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

/-- Uniform real20/52-byte hash caller from a mapped input region, including
all alignment cases and actual input reads. The exact observed digest is
returned and the call consumes one source clock with a pure canonical frame.
No digest/distribution/cryptographic hypothesis enters this runtime contract. -/
theorem call_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind pointer))
    (known : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (fits : pointer.toNat + keySize kind < 2 ^ 64)
    (mapped : ∀ offset < keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset)))
    (enough : 1 ≤ source.clock) :
    ∃ digest : BitVec 64,
      evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") arguments continuation) =
        (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - 1} name digest) continuation
         (output.1, restore source name output.2)) := by
  by_cases aligned : pointer &&& 7#64 = 0#64
  · let words := MemeqSized.wordsOf source pointer
    let bytes := MemeqSized.trailingOf source kind pointer
    have data := MemeqSized.data_of_mapped source kind pointer aligned fits mapped
    exact ⟨resultWord kind words bytes, aligned_call source kind pointer words bytes name arguments continuation args known
      aligned data.mapped data.stored data.trailing enough⟩
  · let bytes : Fin 52 → UInt8 := fun index => MemeqByteRuntime.observed source pointer index.val
    have reads : ∀ index : Fin 52, index.val < keySize kind → @panMemLoadByteHOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be
        (pointer + BitVec.ofNat 64 index.val) = some (bytes index) := by
      intro index inside
      exact MemeqByteRuntime.observed_read source pointer index.val (mapped index.val inside)
    exact ⟨resultWord kind (packedWords bytes) (tailBytes kind bytes),
      unaligned_call source kind pointer bytes name arguments continuation args known aligned reads enough⟩

end InitECandidate.Solver.MutableTable.HashSized

#print axioms InitECandidate.Solver.MutableTable.HashSized.call_of_mapped
