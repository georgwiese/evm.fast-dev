import InitECandidate.Solver.Headers.SliceState
import InitECandidate.Solver.Input.StoreWordsNormal

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

/-- Actual scalar/tuple header stores preserve the entire current RLP
slice invariant when their bounded real word footprint starts after the
record allocation. Mapping and output memory come from the actual normal
store; the value read and word count are current typed-local facts. -/
theorem SliceState.normal_store_after (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array cursor limit address : BitVec 64) (bytes cutoff maximumWords : Nat) (items : List Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items)
    (destination expression : ExpHOL 64) (value : ValueHOL 64)
    (addressRead : eval source destination=some (.val (.word address)))
    (valueRead : eval source expression=some value) (size : (flattenHOL value).length≤maximumWords)
    (afterArray : array.toNat+16*items.length≤address.toNat) (fits : address.toNat+8*maximumWords<2^64)
    (normal : evaluateHOLFiniteState source (.store destination expression)=(none,target)) :
    SliceState target pointer array cursor limit bytes cutoff items ∧ target.locals=source.locals ∧ target.globals=source.globals := by
  obtain ⟨actual,memory,read,stores,post⟩ := Input.store_at_normal source target destination expression address addressRead normal
  have same : actual=value := Option.some.inj (read.symm.trans valueRead)
  subst actual
  have before (query : BitVec 64) (low : query.toNat<address.toNat) : target.memory query=source.memory query := by
    rw [post]
    apply Input.words_away (flattenHOL value) address query source.memaddrs source.memory memory stores
    intro index inside equal
    have number : (address+BitVec.ofNat 64 (8*index)).toNat=address.toNat+8*index :=
      MemoryBytes.offset_toNat address (8*index) (by omega)
    have same:=congrArg BitVec.toNat equal
    rw [number] at same
    omega
  have frame : Rlp.Slices.Window source target address.toNat (2^64) := by
    intro query outside
    apply before query
    rcases outside with low|large
    · exact low
    · have bounded:=query.isLt
      omega
  have small : bytes<2^64 := by have h:=state.inputFits; omega
  have wordSize : (BitVec.ofNat 64 bytes).toNat=bytes := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have domain : target.memaddrs=source.memaddrs := by rw [post]
  have globals : target.globals=source.globals := by rw [post]
  have endian : target.be=source.be := by rw [post]
  have nextArena:=Rlp.Validation.Arena.of_fields source target cursor limit state.arena domain globals
  have nextRecords : Rlp.Slices.Records target.memory array pointer items :=
    Rlp.Slices.Records.of_interval source target array pointer items state.records (by have h:=state.arrayArena.upper; omega)
      (fun query lower upper=>before query (by omega))
  have byteFrame:=frame.bytes_before source target address.toNat (2^64) pointer (BitVec.ofNat 64 bytes)
    (by rw [wordSize]; have h:=state.inputBefore; omega) (by rw [wordSize]; exact state.inputFits) domain endian
  refine ⟨state.of_parts source target pointer array cursor limit bytes cutoff items nextArena nextRecords ?_,by rw [post],globals⟩
  intro offset inside
  exact byteFrame offset (by rw [wordSize]; exact inside)

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.SliceState.normal_store_after
