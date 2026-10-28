import InitECandidate.Solver.Input.VarList.RecordsFrame
import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete physical transaction-list data retained at a particular payload
state, including the actual allocator frontier past the entire record array. -/
structure TransactionImage (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record array : BitVec 64) (start size : Nat) : Prop where
  startEq : start = 62 + Guest.GasLimit.le32 input 566
  sizeEq : size = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566
  inside : start + size ≤ input.length % 2^64
  arrayAfter : record.toNat + 136 ≤ array.toNat
  heapExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) state
  records : VarList.Records state input pointer array start size
  txs : state.memory (record + 32#64) = .word (VarList.decodedArray array size)
  count : state.memory (record + 40#64) = .word (BitVec.ofNat 64 (VarList.decodedCount input start size))

theorem TransactionImage.of_frame {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {start size : Nat}
    (data : TransactionImage input source pointer record array start size)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    TransactionImage input target pointer record array start size := by
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frame
  change target.memory = source.memory at memory
  change target.globals = source.globals at globals
  refine ⟨data.startEq, data.sizeEq, data.inside, data.arrayAfter, ?_,
    VarList.Records.of_memory source target input pointer array start size memory data.records, ?_, ?_⟩
  · obtain ⟨cursor, cell, low, high, aligned⟩ := data.heapExtent
    exact ⟨cursor, (congrArg (fun table => table.lookup (ofString "heap_ptr")) globals).trans cell, low, high, aligned⟩
  · rw [memory]
    exact data.txs
  · rw [memory]
    exact data.count

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.TransactionImage.of_frame
