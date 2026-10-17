import InitECandidate.Solver.MutableTable.ByteStore
import InitECandidate.Solver.MutableTable.ValueModel32
import InitECandidate.Solver.MutableTable.HeaderData

namespace InitECandidate.Solver.MutableTable.MemoryFrame
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem byte_writes_away {F : Type} (source : PanSemStateFiniteExact 64 F)
    (writes : List (BitVec 64×BitVec 64)) (query : BitVec 64)
    (away : panByteAlignHOL (width:=64) query∉writes.map Prod.fst) :
    @panMemLoadByteHOL 64 _ (WordWrites.write source.memory writes) source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be query=
    @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be query := by
  classical
  have same:=WordWrites.write_away source.memory writes (panByteAlignHOL (width:=64) query) away
  simp only [panMemLoadByteHOL,same]

theorem byteView_writes_away {F : Type} (source : PanSemStateFiniteExact 64 F)
    (writes : List (BitVec 64×BitVec 64)) (pointer : BitVec 64) (key : ByteKeys.Key)
    (away : ∀ byte : Fin 32,panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val)∉writes.map Prod.fst)
    (view : MemoryBytes.ByteView source pointer key) :
    MemoryBytes.ByteView {source with memory:=WordWrites.write source.memory writes} pointer key := by
  intro byte
  rw [byte_writes_away source writes _ (away byte)]
  exact view byte

theorem byteView_byte_away {F : Type} (source : PanSemStateFiniteExact 64 F) (address pointer : BitVec 64)
    (byte : UInt8) (key : ByteKeys.Key) (little : source.be=false)
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) address))
    (away : ∀ offset : Fin 32,pointer+BitVec.ofNat 64 offset.val≠address)
    (view : MemoryBytes.ByteView source pointer key) :
    MemoryBytes.ByteView {source with memory:=ByteStore.write source.memory address byte} pointer key := by
  intro offset
  rw [ByteStore.read_write source address _ byte little mapped,if_neg (away offset)]
  exact view offset

theorem values_writes_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (writes : List (BitVec 64×BitVec 64)) (vals : BitVec 64) (capacity : Nat) (table : Find.Model32 (BitVec 64))
    (away : ∀ i<capacity,vals+BitVec.ofNat 64 i*8#64∉writes.map Prod.fst)
    (model : Find.ValueModel32 source vals capacity table) :
    Find.ValueModel32 {source with memory:=WordWrites.write source.memory writes} vals capacity table := by
  intro i inside key value cell
  obtain ⟨mapped,stored⟩:=model i inside key value cell
  exact ⟨mapped,(WordWrites.write_away source.memory writes _ (away i inside)).trans stored⟩

theorem keys_writes_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (writes : List (BitVec 64×BitVec 64)) (p : Find.Parameters) (capacity : Nat) (table : Find.Model32 (BitVec 64))
    (awayUsed : ∀ i<capacity,panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 i)∉writes.map Prod.fst)
    (awayKeys : ∀ i<capacity,∀ byte : Fin 32,
      panByteAlignHOL (width:=64) (p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val)∉writes.map Prod.fst)
    (model : Find.KeyModel32 source p capacity table) :
    Find.KeyModel32 {source with memory:=WordWrites.write source.memory writes} p capacity table := by
  constructor
  · intro i inside
    exact (byte_writes_away source writes _ (awayUsed i inside)).trans (model.used i inside)
  · intro i inside key value cell
    exact byteView_writes_away source writes _ key (awayKeys i inside) (model.view i inside key value cell)

end InitECandidate.Solver.MutableTable.MemoryFrame

#print axioms InitECandidate.Solver.MutableTable.MemoryFrame.byte_writes_away
#print axioms InitECandidate.Solver.MutableTable.MemoryFrame.byteView_byte_away
#print axioms InitECandidate.Solver.MutableTable.MemoryFrame.keys_writes_away
