import InitECandidate.Solver.WitnessRadix.AllocatedAway
import InitECandidate.Solver.MutableTable.LayoutEarlier32
import InitECandidate.Solver.WitnessRadix.MemoryAgreement
import InitECandidate.Solver.HashEnvironmentFrame

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem cell_high (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (pool : Pool)
    (offset : Nat) (inside : offset<size plan pool) : plan.table≤(cell plan pool offset).toNat := by
  rw [number plan ready pool offset inside]
  have :=(bounds plan ready pool).1
  omega

/-- The full represented build survives changes below the private table,
including the actual hash buffers and their event-producing execution. -/
theorem built_high_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (bits : Nat) (keyPointer : BitVec 64) (count : Nat)
    (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (memory : ∀ query,plan.table≤query.toNat→source.memory query=target.memory query)
    (built : Built bits source plan keyPointer count input logical) : Built bits target plan keyPointer count input logical := by
  have headerWord (offset : Nat) (inside : offset<72) :
      target.memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset)=source.memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
    apply Eq.symm
    apply memory
    rw [header_cell]
    exact cell_high plan ready .header offset inside
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩,?_,?_,built.trace,built.countBound⟩
  · intro offset member;rw [← domain];exact built.header.find.mapped offset member
  · exact (headerWord 16 (by decide)).trans built.header.find.capacity
  · simpa only [BitVec.add_zero] using (headerWord 0 (by decide)).trans
      (show source.memory (BitVec.ofNat 64 plan.table+0#64)=.word (parameters plan keyPointer).keyLength by simpa using built.header.find.keyLength)
  · exact (headerWord 8 (by decide)).trans built.header.find.stride
  · exact (headerWord 32 (by decide)).trans built.header.find.keys
  · exact (headerWord 48 (by decide)).trans built.header.find.used
  · exact (headerWord 40 (by decide)).trans built.header.values
  · exact (headerWord 56 (by decide)).trans built.header.order
  · exact (headerWord 64 (by decide)).trans built.header.position
  · exact (headerWord 24 (by decide)).trans built.header.count
  · constructor
    · intro i inside
      have wordEq : source.memory (panByteAlignHOL (width:=64) ((parameters plan keyPointer).used+BitVec.ofNat 64 i))=
          target.memory (panByteAlignHOL (width:=64) ((parameters plan keyPointer).used+BitVec.ofNat 64 i)) := by
        apply memory
        rw [used_byte_cell plan ready keyPointer i inside]
        exact cell_high plan ready .used _ (by change _<plan.capacity;omega)
      exact (MemoryBytes.read_of_cell source target domain endian _ wordEq).symm.trans (built.keys.used i inside)
    · intro i inside key value cell
      apply MemoryBytes.byteView_of_cells source target domain endian _ key _ (built.keys.view i inside key value cell)
      intro byte
      apply memory
      rw [key_byte_cell plan ready keyPointer i byte.val inside byte.isLt]
      exact cell_high plan ready .keys _ (by change _<32*plan.capacity;have:=byte.isLt;omega)
  · intro i inside key value cell
    obtain ⟨mapped,stored⟩:=built.values i inside key value cell
    rw [domain] at mapped
    refine ⟨mapped,?_⟩
    have wordEq:=memory (BitVec.ofNat 64 (base plan .values)+BitVec.ofNat 64 i*8#64) (by
      rw [value_cell];exact cell_high plan ready .values _ (by change _<8*plan.capacity;omega))
    exact wordEq.symm.trans stored

/-- The actual complete keccak call's protected-memory theorem preserves
the original table invariant whenever all three write buffers precede it. -/
theorem built_after_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (bits : Nat) (keyPointer : BitVec 64) (count : Nat)
    (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (stp pointer scratch out : BitVec 64) (length : Nat) (buffers : Keccak256.Buffers stp pointer scratch out length)
    (before : stp.toNat+200≤plan.table ∧ scratch.toNat+136≤plan.table ∧ out.toNat+32≤plan.table)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source)
    (memory : ∀ query,Keccak256.Protected stp scratch out query→target.memory query=source.memory query)
    (built : Built bits source plan keyPointer count input logical) : Built bits target plan keyPointer count input logical := by
  have domain : target.memaddrs=source.memaddrs:=congrArg (fun state=>state.memaddrs) control
  have endian : target.be=source.be:=congrArg (fun state=>state.be) control
  apply built_high_frame source target plan ready bits keyPointer count input logical domain.symm endian.symm _ built
  intro query high
  apply Eq.symm
  apply memory
  exact AllocatedBytes.protected_above stp pointer scratch out query length buffers
    (by omega) (by omega) (by omega)

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.built_high_frame
#print axioms InitECandidate.Solver.MutableTable.Layout32.built_after_hash
