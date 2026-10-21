import InitECandidate.Solver.MutableTable.WitnessDictionaryLookup

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
attribute [local instance] Classical.propDecidable

/-- Physical runtime data for the original immutable witness table at any
query pointer. The covering list comes from construction history. -/
structure RuntimeTable (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (query : BitVec 64) (bits : Nat) (order : List Nat) : Prop where
  small : bits<64
  capacity : (Layout32.parameters plan query).capacity=BitVec.ofNat 64 (2^bits)
  header : Find.HeaderData source (BitVec.ofNat 64 plan.table) (Layout32.parameters plan query)
  room : order.length<2^bits
  binary : ∀ i<2^bits,Find.usedByte source (Layout32.parameters plan query) (BitVec.ofNat 64 i)=some 0 ∨
    Find.usedByte source (Layout32.parameters plan query) (BitVec.ofNat 64 i)=some 1
  covered : ∀ i<2^bits,Find.usedByte source (Layout32.parameters plan query) (BitVec.ofNat 64 i)=some 1→i∈order
  fits : ∀ i<2^bits,((Layout32.parameters plan query).keys+BitVec.ofNat 64 i*(Layout32.parameters plan query).stride).toNat+32<2^64
  mapped : ∀ i<2^bits,∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64)
    (byteAddress ((Layout32.parameters plan query).keys+BitVec.ofNat 64 i*(Layout32.parameters plan query).stride) offset))
  valsMapped : source.memaddrs (BitVec.ofNat 64 plan.table+40#64)
  valsCell : source.memory (BitVec.ofNat 64 plan.table+40#64)=.word (BitVec.ofNat 64 (Layout32.base plan .values))
  values : ∀ slot : BitVec 64,slot.toNat<(Layout32.parameters plan query).capacity.toNat→∃ value,
    source.memaddrs (BitVec.ofNat 64 (Layout32.base plan .values)+slot*8#64) ∧
    source.memory (BitVec.ofNat 64 (Layout32.base plan .values)+slot*8#64)=.word value

/-- Genuine constructor layout/history supplies the entire physical lookup
context without requiring any query read. All key slots and value cells are
owned by the actual successful allocation. -/
theorem runtime_of_built (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits) (scratch : BitVec 64) (count : Nat)
    (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (built : Layout32.Built bits source plan scratch count input logical) (history : History plan input) (query : BitVec 64) :
    ∃ order,order.length≤input.length ∧ RuntimeTable source plan query bits order := by
  let p:=Layout32.parameters plan query
  obtain ⟨order,lengthBound,covered⟩ := Placement.build_cover plan.capacity (Find.hashHome bits) input logical built.trace
  have inputBound:=history.length_bound plan input
  have room:=ready.room
  have header : Find.HeaderData source (BitVec.ofNat 64 plan.table) p :=
    ⟨built.header.find.mapped,built.header.find.capacity,built.header.find.keyLength,built.header.find.stride,built.header.find.keys,built.header.find.used⟩
  have capSmall : plan.capacity<2^64 := by rw [power]; exact Nat.pow_lt_pow_right (by decide) small
  have capNumber : p.capacity.toNat=plan.capacity := by
    change (BitVec.ofNat 64 plan.capacity).toNat=plan.capacity
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
  have sameUsed (index : BitVec 64) : Find.usedByte source (Layout32.parameters plan scratch) index=
      Find.usedByte source (Layout32.parameters plan query) index := rfl
  refine ⟨order,lengthBound,small,by change BitVec.ofNat 64 plan.capacity=_; rw [power],header,by omega,?_,?_,?_,?_,?_,built.header.values,?_⟩
  · intro i inside
    have actual:=built.keys.used i (by rwa [power])
    rw [sameUsed] at actual
    cases cell : logical i with
    | none => exact Or.inl (by simpa only [cell] using actual)
    | some entry => exact Or.inr (by simpa only [cell] using actual)
  · intro i inside one
    apply covered i (by rwa [power])
    intro empty
    have actual:=built.keys.used i (by rwa [power])
    rw [sameUsed] at actual
    rw [empty] at actual
    rw [actual] at one
    cases one
  · intro i inside
    exact Layout32.key_fits plan ready query i (by rwa [power])
  · intro i inside offset offsetInside
    change source.memaddrs (panByteAlignHOL (width:=64) ((Layout32.parameters plan query).keys+BitVec.ofNat 64 i*(Layout32.parameters plan query).stride+BitVec.ofNat 64 offset))
    rw [Layout32.key_byte_cell plan ready query i offset (by rwa [power]) offsetInside]
    exact Layout32.word_mapped source plan ready domain .keys _ (by change _<32*plan.capacity; rw [power]; omega) (by omega)
  · rw [Layout32.header_cell plan 40]
    exact Layout32.word_mapped source plan ready domain .header 40 (by change 40<72; decide) (by decide)
  · intro slot inside
    have slotInside : slot.toNat<plan.capacity := by rwa [capNumber] at inside
    have address : BitVec.ofNat 64 (Layout32.base plan .values)+slot*8#64=Layout32.cell plan .values (8*slot.toNat) := by
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using Layout32.value_cell plan slot.toNat
    have mapped : source.memaddrs (BitVec.ofNat 64 (Layout32.base plan .values)+slot*8#64) := by
      rw [address]
      exact Layout32.word_mapped source plan ready domain .values _ (by change _<8*plan.capacity; omega) (by omega)
    cases stored : source.memory (BitVec.ofNat 64 (Layout32.base plan .values)+slot*8#64) with
    | word value => exact ⟨value,mapped,rfl⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.runtime_of_built
