import InitECandidate.Solver.MutableTable.HashSizedMapped
import InitECandidate.Solver.MutableTable.HashByteRuntime.Call
import InitECandidate.Solver.MutableTable.HashMemory32

namespace InitECandidate.Solver.MutableTable.KeyHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

/-- Exactly the key widths used by original table constructors. -/
inductive Kind where | account | indexedAccount | word | storage | indexedStorage
  deriving DecidableEq

def keySize : Kind → Nat | .account => 20 | .indexedAccount => 28 | .word => 32 | .storage => 52 | .indexedStorage => 60
def hashPrice : Kind → Nat
  | .indexedAccount => MemeqByteRuntime.price 28 + 1
  | .indexedStorage => MemeqByteRuntime.price 60 + 1
  | _ => 1
def values (kind : Kind) (pointer : BitVec 64) : List (ValueHOL 64) :=
  [.val (.word pointer), .val (.word (BitVec.ofNat 64 (keySize kind)))]

def observedKey (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : ByteKeys.Key :=
  fun byte => ByteRegion.value source (byteAddress pointer byte.val)

theorem observed_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (mapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset))) :
    MemoryBytes.ByteView source pointer (observedKey source pointer) := by
  intro byte
  have actual := MemeqByteRuntime.observed_read source pointer byte.val (mapped byte.val byte.isLt)
  simpa only [MemeqByteRuntime.observed, observedKey, Memeq32.toUInt8, UInt8.ofNat_bitVecToNat, byteAddress] using actual

theorem key_size_small (kind : Kind) : keySize kind ≤ 64 := by cases kind <;> decide
theorem hash_price_positive (kind : Kind) : 0 < hashPrice kind := by cases kind <;> decide

/-- Uniform real hash caller for every key width in the unchanged program.
The observed digest is returned without a collision/distribution assumption.
Mapped-byte/no-wrap/code/endian/clock entry conditions remain explicit. -/
theorem call_of_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (pointer : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind pointer))
    (known : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (fits : pointer.toNat + keySize kind < 2 ^ 64)
    (mapped : ∀ offset < keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset)))
    (little : source.be = false) (enough : hashPrice kind ≤ source.clock) :
    ∃ digest, evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_hash") arguments continuation) =
      (let output := evaluateHOLFiniteState (WitnessRadix.QueryBranch.bind {source with clock := source.clock - hashPrice kind} name digest) continuation
       (output.1, restore source name output.2)) := by
  cases kind with
  | account => exact HashSized.call_of_mapped source .address pointer name arguments continuation args known fits mapped enough
  | storage => exact HashSized.call_of_mapped source .storage pointer name arguments continuation args known fits mapped enough
  | indexedAccount => exact HashByteRuntime.call_of_mapped source pointer 28 name arguments continuation args known (by decide) (by decide) (by decide) (by decide) mapped enough
  | indexedStorage => exact HashByteRuntime.call_of_mapped source pointer 60 name arguments continuation args known (by decide) (by decide) (by decide) (by decide) mapped enough
  | word => exact ⟨Hash.keyHash (observedKey source pointer), Hash.memory_call source pointer (observedKey source pointer) name arguments continuation
      args known (observed_view source pointer mapped) fits little enough⟩

end InitECandidate.Solver.MutableTable.KeyHash

#print axioms InitECandidate.Solver.MutableTable.KeyHash.observed_view
#print axioms InitECandidate.Solver.MutableTable.KeyHash.key_size_small
#print axioms InitECandidate.Solver.MutableTable.KeyHash.hash_price_positive
#print axioms InitECandidate.Solver.MutableTable.KeyHash.call_of_mapped
