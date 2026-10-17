import InitECandidate.Solver.MutableTable.ZeroBytes
import InitECandidate.Solver.MutableTable.HeaderData
import InitECandidate.Solver.WitnessRadix.TableMemory

namespace InitECandidate.Solver.MutableTable.TableEmpty
open Flapjack PanSemStateFiniteExact WitnessRadix

def parameters (plan : AllocatedLayout.Plan) (key : BitVec 64) : Find.Parameters where
  capacity:=BitVec.ofNat 64 plan.capacity
  keyLength:=32#64
  stride:=32#64
  keys:=BitVec.ofNat 64 (plan.table+72)
  used:=TableNew.usedAddress plan
  key:=key

theorem used_number (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) :
    (TableNew.usedAddress plan).toNat=plan.table+72+40*plan.capacity := by
  have fits:=ready.fits
  rw [TableNew.usedAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]

theorem used_aligned (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) :
    (TableNew.usedAddress plan).toNat%8=0 := by
  rw [used_number plan ready]
  have aligned:=ready.tableAligned
  omega

theorem cleared_byte (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (offset : Nat) (inside : offset<plan.capacity) :
    ZeroBytes.read (TableNew.clearMemory memory false plan) (TableNew.usedAddress plan+BitVec.ofNat 64 offset)=0 := by
  have fits:=ready.fits
  by_cases four : plan.capacity=4
  · simpa only [TableNew.clearMemory,if_pos four,Nat.zero_add] using
      ZeroBytes.memoryByte_cell memory (TableNew.usedAddress plan) 0 plan.capacity offset inside
  · simp only [TableNew.clearMemory,if_neg four]
    exact ZeroBytes.final_byte memory _ plan.capacity offset (shape.resolve_left four) inside
      (used_aligned plan ready) (by rw [used_number plan ready];omega)

/-- The three final header writes preserve every cleared used byte. -/
theorem result_byte (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (offset : Nat) (inside : offset<plan.capacity) :
    ZeroBytes.read (TableNew.resultMemory memory false plan) (TableNew.usedAddress plan+BitVec.ofNat 64 offset)=0 := by
  have fits:=ready.fits
  have number:=MemoryBytes.offset_toNat (TableNew.usedAddress plan) offset
    (by rw [used_number plan ready];omega)
  rw [used_number plan ready] at number
  have aligned:=used_aligned plan ready
  rw [used_number plan ready] at aligned
  have beyond : plan.table+72≤(panByteAlignHOL (width:=64) (TableNew.usedAddress plan+BitVec.ofNat 64 offset)).toNat := by
    rw [ByteStore.aligned_number,number]
    omega
  have away : panByteAlignHOL (width:=64) (TableNew.usedAddress plan+BitVec.ofNat 64 offset)∉
      (TableNew.afterWrites plan).map Prod.fst := by
    rw [TableNew.after_cells]
    intro member
    obtain ⟨entry,member,same⟩:=List.mem_map.mp member
    have header : entry.1=BackingLayout.Pool.header ∧ entry.2<72 := by
      simp only [TableNew.afterSites,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    obtain ⟨pool,index⟩:=entry
    change pool=BackingLayout.Pool.header ∧ index<72 at header
    rcases header with ⟨rfl,bound⟩
    have equal:=congrArg BitVec.toNat same
    change (BackingLayout.cell (AllocatedLayout.layout plan) .header index).toNat=_ at equal
    rw [TableNew.header_number plan ready index bound] at equal
    omega
  unfold ZeroBytes.read TableNew.resultMemory
  rw [WordWrites.write_away _ _ _ away]
  exact cleared_byte _ plan ready shape offset inside

/-- A byte of the completed original constructor is mapped and really loads
zero, including cap=4's byte-store clearing path. -/
theorem result_load {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (offset : Nat) (inside : offset<plan.capacity) :
    @panMemLoadByteHOL 64 _ (TableNew.resultMemory source.memory source.be plan) source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (TableNew.usedAddress plan+BitVec.ofNat 64 offset)=some 0 := by
  classical
  have fits:=ready.fits
  have room:=ready.room
  have lower:=ready.recordsLower
  have records:=ready.recordsBefore
  have number:=MemoryBytes.offset_toNat (TableNew.usedAddress plan) offset
    (by rw [used_number plan ready];omega)
  rw [used_number plan ready] at number
  have aligned:=used_aligned plan ready
  have cellNumber:=ByteStore.aligned_number (TableNew.usedAddress plan+BitVec.ofNat 64 offset)
  rw [number] at cellNumber
  have usedAligned:=aligned
  rw [used_number plan ready] at usedAligned
  have mapped : source.memaddrs (panByteAlignHOL (width:=64) (TableNew.usedAddress plan+BitVec.ofNat 64 offset)) := by
    rw [domain]
    apply BackingLayout.ordinary_mapped _ (by rw [cellNumber];omega) (by rw [cellNumber];omega)
    rw [cellNumber];omega
  have read:=result_byte source.memory plan ready shape offset inside
  rw [little]
  cases stored : TableNew.resultMemory source.memory false plan
      (panByteAlignHOL (width:=64) (TableNew.usedAddress plan+BitVec.ofNat 64 offset)) with
  | word value=>
    simp only [ZeroBytes.read,stored,MemoryBytes.wordBits] at read
    simp only [panMemLoadByteHOL,stored,if_pos mapped,read]

/-- The real constructor establishes the physical representation of the
empty original dictionary, before any record is inserted. -/
theorem entered_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (shape : plan.capacity=4 ∨ plan.capacity%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false) (key : BitVec 64) :
    Find.KeyModel32 (TableNew.enteredState source plan) (parameters plan key) plan.capacity
      (fun _=>none : Find.Model32 (BitVec 64)) := by
  constructor
  · intro i inside
    change @panMemLoadByteHOL 64 _ (TableNew.enteredState source plan).memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (TableNew.usedAddress plan+BitVec.ofNat 64 i)=some 0
    rw [TableNew.entered_memory]
    exact result_load source plan ready shape domain little i inside
  · intro i inside key value impossible
    cases impossible

end InitECandidate.Solver.MutableTable.TableEmpty

#print axioms InitECandidate.Solver.MutableTable.TableEmpty.result_byte
#print axioms InitECandidate.Solver.MutableTable.TableEmpty.result_load
#print axioms InitECandidate.Solver.MutableTable.TableEmpty.entered_model
