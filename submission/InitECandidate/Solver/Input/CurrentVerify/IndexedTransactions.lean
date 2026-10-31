import InitECandidate.Solver.Input.CurrentVerify.BlockSizeGuard
import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderTrieEntry
import InitECandidate.Solver.Input.CurrentVerify.TransactionNonempty
import InitECandidate.Solver.Input.VarList.ArrayGeometry
import InitECandidate.Solver.Mpt.CurrentIndexedSetup
import InitECandidate.Solver.Input.CurrentVerify.DataMetadata
import InitECandidate.Solver.Input.HeaderEncoding.FieldFrame
import InitECandidate.Solver.WitnessRadix.AllocatedAwayBelow

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
namespace PayloadHeaderEntry

/-- Retain the same physical header through an actual normal writer
whose metadata and caller locals are restored and whose writes lie beyond
the header's 31 cells. This also retains the whole earlier decoded input. -/
theorem PhysicalHeader.of_older {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (frame : MemoryMetadata.erase target=MemoryMetadata.erase current) (localsEq : target.locals=current.locals)
    (memory : ∀ query : BitVec 64,query.toNat<header.toNat+248→target.memory query=current.memory query) :
    PhysicalHeader input source target pointer si record gasWord boundary header := by
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=current.globals at globalsEq
  have domain:=MemoryMetadata.domain frame
  change target.memaddrs=current.memaddrs at domain
  have endian:=MemoryMetadata.endian frame
  change target.be=current.be at endian
  have code:=MemoryMetadata.code frame
  change target.code=current.code at code
  have cells (offset : Nat) (small : offset≤240) : target.memory (HeaderEncoding.address header offset)=current.memory (HeaderEncoding.address header offset):=by
    apply memory
    have number:=byteAddress_toNat header offset (by have upper:=physical.buffers.ommer.headerArena.upper; omega)
    change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at number
    change (header+BitVec.ofNat 64 offset).toNat<header.toNat+248
    omega
  exact {
    data:=physical.data.of_metadata frame (by rw [localsEq]; exact physical.data.siLocal)
      (fun query lower before=>memory query (by have headerBefore:=physical.before; omega))
    frame:={
      code:=code.trans physical.frame.code,domain:=domain.trans physical.frame.domain,endian:=endian.trans physical.frame.endian
      globals:=fun name other=>by rw [globalsEq]; exact physical.frame.globals name other
      header:=by rw [localsEq]; exact physical.frame.header
      raw:=by rw [localsEq]; exact physical.frame.raw
      payload:=by rw [localsEq]; exact physical.frame.payload
      si:=by rw [localsEq]; exact physical.frame.si
      older:=fun query lower before=>(memory query (by omega)).trans (physical.frame.older query lower before) }
    buffers:=physical.buffers,frontier:=physical.frontier.of_globals current target header (headerFrontier header) globalsEq,entryHeap:=physical.entryHeap
    before:=physical.before,geometry:=physical.geometry
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.fields field member)
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.optional field member)
    locals:=⟨by rw [localsEq]; exact physical.locals.transactions,by rw [localsEq]; exact physical.locals.withdrawals,
      by rw [localsEq]; exact physical.locals.requests,by rw [localsEq]; exact physical.locals.balance⟩ }

/-- The observed literal transaction-trie caller retains the complete
physical header and proves that the actual decoded transaction count is
zero. Its entry, normal callee and restored caller all belong to this run. -/
theorem PhysicalHeader.transaction_normal {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input)
    (normal : evaluateHOLFiniteState current transactionTrieCall=(none,target)) :
    VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0 ∧ PhysicalHeader input source target pointer si record gasWord boundary header ∧ target.locals=current.locals := by
  obtain ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩:=physical.transaction_entry checked
  obtain ⟨funded,child,returned,run⟩:=CallNormal.ignored_callee_return current target (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one args called normal
  obtain ⟨zero,answer,domain,endian,code,heapCell,globals,metadata,memory⟩:=Mpt.CurrentIndexed.body_normal entry roots returned run
  have endpoint:=CallNormal.ignored_target current target (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one args called returned child run normal
  have heapEq : entry.heap=headerFrontier header:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using entry.heapCell.symm.trans physical.frontier.cell
  have numbers:=physical.buffers.numbers header
  have outputAligned : (afterOmmerHeap header).toNat%8=0:=by rw [numbers.transactions]; have aligned:=physical.buffers.ommer.headerAligned; omega
  rw [endpoint]
  refine ⟨countEq.symm.trans zero,physical.of_older metadata rfl ?_,rfl⟩
  intro query before
  apply memory query
  · rw [heapEq,numbers.frontier]; omega
  · exact physical.buffers.transactions.away_below (afterOmmerHeap header) query 32 outputAligned (by rw [numbers.transactions]; omega)

/-- Main's literal first transaction-trie caller instantiates the complete
current builder allowance from its same decoded scan/header/startup evidence. -/
theorem PhysicalHeader.transaction_cost {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input) :
    current.clock-(evaluateHOLFiniteState current transactionTrieCall).2.clock≤463385007916 := by
  obtain ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩:=physical.transaction_entry checked
  exact ClockCost.call_current current (some none) (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one 463385007915
    args called (Mpt.CurrentIndexed.uniform_body_cost entry roots countBound)

/-- The whole actual payload-header execution through its transaction
trie either stops within the combined allowance or reaches its unchanged
withdrawal suffix with zero transactions and all original physical inputs. -/
theorem to_after_transaction {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤463781938977 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header current inner encoded,PhysicalHeader input source current pointer si record gasWord boundary header ∧
        VarList.decodedCount input (62+Guest.GasLimit.le32 input 566) (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)=0 ∧
        encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
        current.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤463781938977 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current afterTransactionTrie=(outcome,inner) := by
  rcases to_trie data outcome actual with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨header,entered,inner,encoded,physical,encodedBound,withdrawalBound,number,bl,forward,price,endpoint,remaining⟩:=reached
    rw [transaction_trie_shape,evaluateHOLFiniteState_seq_line780] at remaining
    have callPrice:=physical.transaction_cost checked
    have callForward:=evaluateHOLFiniteState_clock_le entered transactionTrieCall
    have never:=NoReturn.ignored_call (ofString "build_mpt_indexed") transactionTrieArguments entered
    generalize computed : evaluateHOLFiniteState entered transactionTrieCall=output at callPrice callForward remaining never
    obtain ⟨result,current⟩:=output
    change entered.clock-current.clock≤463385007916 at callPrice
    change current.clock≤entered.clock at callForward
    cases result with
    | none=>
      obtain ⟨zero,retained,localsEq⟩:=physical.transaction_normal checked computed
      exact Or.inr ⟨header,current,inner,encoded,retained,zero,encodedBound,withdrawalBound,number,
        by rw [localsEq]; exact bl,Nat.le_trans callForward forward,by omega,endpoint,remaining⟩
    | some result=>
      have observed:=congrArg Prod.fst remaining
      have clocks:=congrArg (fun output=>output.2.clock) remaining
      change current.clock=inner.clock at clocks
      refine Or.inl ⟨by rw [endpoint.clock,←clocks]; omega,?_⟩
      intro value returned
      apply never value
      change (evaluateHOLFiniteState entered transactionTrieCall).1=some (.returned value)
      rw [computed]
      exact observed.trans returned

end PayloadHeaderEntry
end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.indexed_transactions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.transaction_trie_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.of_older
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.transaction_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.to_after_transaction
