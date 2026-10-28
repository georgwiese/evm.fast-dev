import InitECandidate.Solver.Input.CurrentHash.PayloadTransactionMemory
import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.Input.VarList.RecordByteBudget

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def decodedPointers (input : Guest.InputBlob) (blob : BitVec 64) (start : Nat) := VarList.recordPointer input blob start
def decodedLengths (input : Guest.InputBlob) (start size : Nat) (index : Nat) :=
  (VarList.recordLength input start size (VarList.decodedCount input start size) index).toNat

theorem decoded_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (blob array : BitVec 64) (start size : Nat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (records : VarList.Records source input blob array start size) :
    Image source (VarList.decodedArray array size) (decodedPointers input blob start) (decodedLengths input start size) (VarList.decodedCount input start size) := by
  have cells := records.cells source input blob array start size domain
  constructor
  intro index inside
  have pointer := records.pointer_cells source input blob array start size index inside
  have length := (cells.2.2 index inside).2
  simpa only [VarList.row,VarList.lengthCell,decodedPointers,decodedLengths,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_assoc] using And.intro pointer length

/-- Current physical record geometry comes from the same normal decoder,
plus the real parent root-array allocation and current heap frontier. -/
theorem decoded_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (blob array roots cursor chunk : BitVec 64) (start size : Nat) (domain : source.memaddrs=InitE.ordinaryDomain)
    (records : VarList.Records source input blob array start size) (sizeBound : size≤251655056)
    (afterArray : array.toNat+16*VarList.decodedCount input start size≤roots.toNat) (chunkBefore : chunk.toNat+32≤array.toNat)
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0)
    (rootsArena : AllocatedBytes.Arena roots (32*VarList.decodedCount input start size)) (rootsAligned : roots.toNat%8=0)
    (rootsBefore : roots.toNat+32*VarList.decodedCount input start size≤cursor.toNat) :
    Geometry (VarList.decodedArray array size) roots cursor chunk (decodedPointers input blob start) (decodedLengths input start size) (VarList.decodedCount input start size) size := by
  have counts := records.cells source input blob array start size domain
  have sizes := records.size_bounds source input blob array start size
  have arrays (positive : 0<VarList.decodedCount input start size) :
      VarList.decodedArray array size=array ∧ 2701131776≤array.toNat ∧ array.toNat%8=0 ∧ array.toNat+16*VarList.decodedCount input start size≤33806089496 := by
    have nonempty : size≠0 := by intro empty; simp [VarList.decodedCount,empty] at positive
    have actual := records.array_geometry source input blob array start size nonempty
    exact ⟨by simp [VarList.decodedArray,nonempty],actual.2.1,actual.2.2.1,actual.2.2.2.1⟩
  refine ⟨by omega,sizeBound,sizes.2,?_,?_,?_,?_,chunkArena,chunkAligned,rootsArena,rootsAligned,rootsBefore,?_⟩
  · intro positive
    have data := arrays positive
    rw [data.1]
    exact ⟨data.2.1,data.2.2.2⟩
  · by_cases empty : size=0
    · simp [VarList.decodedArray,empty]
    · simp only [VarList.decodedArray,if_neg empty]
      exact (records.array_geometry source input blob array start size empty).2.2.1
  · intro positive
    rw [(arrays positive).1]
    exact afterArray
  · intro positive
    rw [(arrays positive).1]
    exact chunkBefore
  · intro index inside
    exact (records.slice_geometry source input blob array start size index inside).2.2.1

/-- Real item bytes and the offset table share one encoded input budget. -/
theorem decoded_byte_budget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (blob array : BitVec 64) (start size : Nat) (records : VarList.Records source input blob array start size) :
    VarList.sumPrefix (decodedLengths input start size) (VarList.decodedCount input start size)+4*VarList.decodedCount input start size≤size :=
  records.byte_budget source input blob array start size

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.decoded_image
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.decoded_geometry
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.decoded_byte_budget
