import InitECandidate.Solver.Input.CurrentVerify.RunInputs
import InitECandidate.Solver.Input.RlpLength.EntryDeclarations
import InitECandidate.Solver.Input.PayloadWithdrawalNumbers

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def withdrawalStart (input : Guest.InputBlob):=62+Guest.GasLimit.le32 input 570

/-- Earlier real decoder evidence supplies every byte, record and payload
cell used by the current block-length calculation. The mathematical input
list is unrestricted; only its actual encoded extent is bounded. -/
structure BlockInputs (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record array : BitVec 64) (boundary start size : Nat) : Prop where
  data : RlpLength.Block.Data source input pointer array record start size (withdrawalStart input) (Payload.withdrawalCount input)
  inputBound : input.length%2^64≤251655056
  inputBefore : pointer.toNat+input.length%2^64≤boundary
  arrayBefore : array.toNat+16*VarList.decodedCount input start size≤boundary
  cellsBefore : ∀ offset∈([32,40,48,56] : List Nat),(record+BitVec.ofNat 64 offset).toNat<boundary
  txCount : VarList.decodedCount input start size≤12582752
  wdCount : Payload.withdrawalCount input≤(input.length%2^64)/44

/-- Nothing about a later header or RLP return is assumed. The actual
allocator frontier and retained decoder images imply this complete contract. -/
theorem Data.block_inputs {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    ∃ array start size,BlockInputs input source pointer record array boundary start size := by
  obtain ⟨array,length,start,size,payload,arrayBefore,txCount,txBytes⟩:=data.payload
  obtain ⟨cursor,heap,lower,upper,aligned⟩:=data.heap
  have inputBound : input.length%2^64≤251655056:=by
    have copiedLower:=data.copied.lower
    have copiedBefore:=data.copied.beforeRecord
    have recordBefore:=data.recordInside.2
    omega
  have inputBefore : pointer.toNat+input.length%2^64≤boundary:=by
    have copiedBefore:=data.copied.beforeRecord
    have recordBefore:=data.recordInside.2
    omega
  have lengthNumber : (BitVec.ofNat 64 length).toNat=length:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have lengthBound:=payload.sliceUpper
    omega
  have inside : 62+length≤input.length%2^64:=by
    have lengthBound:=payload.sliceUpper
    have positive:=payload.minimum
    omega
  have wdBound:=Payload.withdrawal_count_bound input (BitVec.ofNat 64 length) payload.valid (by rw [lengthNumber]; exact inside)
  have wdSmall : Payload.withdrawalCount input<2^31:=by omega
  obtain ⟨count,remaining,division,remainder⟩:=payload.remaining
  have withdrawalFacts:=Payload.withdrawal_difference input (BitVec.ofNat 64 length) payload.valid
  have countNumber : count.toNat=Payload.withdrawalCount input:=by rw [division,withdrawalFacts.2.1]; rfl
  have countWord : count=BitVec.ofNat 64 (Payload.withdrawalCount input):=by
    calc count=BitVec.ofNat 64 count.toNat:=by simp
         _=BitVec.ofNat 64 (Payload.withdrawalCount input):=by rw [countNumber]
  have balancesUpper : Guest.GasLimit.le32 input 590≤length:=by
    have last:=(payload.valid 3 (by decide)).2.1
    have number : (Payload.offsetWords input 3).toNat=Guest.GasLimit.le32 input 590:=by
      simpa [Payload.offsetWords] using RawScalar.le32_number input 590
    rw [number,lengthNumber] at last
    exact last
  have cellsBefore (offset : Nat) (member : offset∈([32,40,48,56] : List Nat)) : (record+BitVec.ofNat 64 offset).toNat<boundary:=by
    have small : offset<136:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    have number : (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset:=byteAddress_toNat record offset (by have room:=data.recordArena.upper; omega)
    rw [number]
    have recordBefore:=data.recordInside.2
    omega
  refine ⟨array,start,size,?_,inputBound,inputBefore,arrayBefore,cellsBefore,txCount,wdBound⟩
  refine ⟨by have sliceInside:=payload.transactions.inside; omega,wdSmall,data.copied.bytes,payload.transactions.records,?_,?_,payload.transactions.txs,payload.transactions.count,?_,?_⟩
  · unfold withdrawalStart Payload.withdrawalCount
    have ordered:=withdrawalFacts.1
    omega
  · intro offset member
    have small : offset<136 ∧ offset%8=0:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    exact AllocatedBytes.word_mapped source record 136 offset data.arena.domain data.recordArena small.1 data.recordAligned small.2
  · simpa [withdrawalStart,Payload.offsetWords,BitVec.ofNat_add,BitVec.add_assoc] using remaining.hash_fields.1
  · rw [←countWord]
    exact remaining.hash_fields.2.1

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.block_inputs
