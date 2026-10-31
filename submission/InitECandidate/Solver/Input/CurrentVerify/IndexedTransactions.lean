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

/-- Preserve the actual decoded/header band through a normal helper that
restores the entering heap. Hash workspaces below that band may change. -/
theorem PhysicalHeader.of_heap_band {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (domain : target.memaddrs=current.memaddrs) (endian : target.be=current.be) (code : target.code=current.code)
    (globals : HeapGlobals current target)
    (heap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (headerFrontier header))))
    (localsEq : target.locals=current.locals)
    (memory : ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<header.toNat+248→target.memory query=current.memory query) :
    PhysicalHeader input source target pointer si record gasWord boundary header := by
  have headerAbove : 2701134824≤header.toNat:=by
    have a:=physical.data.recordInside.1; have b:=physical.data.recordInside.2; have c:=physical.before; omega
  have cells (offset : Nat) (small : offset≤240) : target.memory (HeaderEncoding.address header offset)=current.memory (HeaderEncoding.address header offset):=by
    have number:=byteAddress_toNat header offset (by have upper:=physical.buffers.ommer.headerArena.upper; omega)
    change (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset at number
    apply memory
    · change 2701134824≤(header+BitVec.ofNat 64 offset).toNat
      omega
    · change (header+BitVec.ofNat 64 offset).toNat<header.toNat+248
      omega
  have nextHeap : NormalHeapEffects.AtLeast (boundary+32) target:=
    ⟨headerFrontier header,heap,by have a:=physical.before; have b:=physical.frontier.afterHeader; omega,
      physical.frontier.bounded,physical.frontier.aligned⟩
  exact {
    data:=physical.data.of_heap_frame domain endian code globals nextHeap
      (by rw [localsEq]; exact physical.data.siLocal)
      (fun query above before=>memory query above (by have a:=physical.before; omega))
    frame:={
      code:=code.trans physical.frame.code,domain:=domain.trans physical.frame.domain,endian:=endian.trans physical.frame.endian
      globals:=fun name other=>(globals name other).trans (physical.frame.globals name other)
      header:=by rw [localsEq]; exact physical.frame.header
      raw:=by rw [localsEq]; exact physical.frame.raw
      payload:=by rw [localsEq]; exact physical.frame.payload
      si:=by rw [localsEq]; exact physical.frame.si
      older:=fun query above before=>(memory query above (by omega)).trans (physical.frame.older query above before) }
    buffers:=physical.buffers,frontier:={physical.frontier with cell:=heap},entryHeap:=physical.entryHeap
    before:=physical.before,geometry:=physical.geometry
    fields:=fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.fields field member)
    optional:=fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory target.memory header field cells (physical.optional field member)
    locals:=⟨by rw [localsEq]; exact physical.locals.transactions,by rw [localsEq]; exact physical.locals.withdrawals,
      by rw [localsEq]; exact physical.locals.requests,by rw [localsEq]; exact physical.locals.balance⟩ }

/-- The actual transaction-trie call retains the complete physical header
for every decoded transaction count, including nonempty tries. -/
theorem PhysicalHeader.transaction_normal {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input)
    (normal : evaluateHOLFiniteState current transactionTrieCall=(none,target)) :
    PhysicalHeader input source target pointer si record gasWord boundary header ∧ target.locals=current.locals := by
  obtain ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩:=physical.transaction_entry_owned checked
  have heapEq : entry.heap=headerFrontier header:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using entry.heapCell.symm.trans physical.frontier.cell
  have before : boundary≤(headerFrontier header).toNat:=by
    have a:=physical.before; have b:=physical.frontier.afterHeader; omega
  let expanded:=entry.widen (nextLimit:=251655056) (nextEnd:=(headerFrontier header).toNat) (Nat.le_refl _) before
  have inputBefore : (headerFrontier header).toNat≤expanded.heap.toNat:=by change _≤entry.heap.toNat; rw [heapEq]
  have numbers:=physical.buffers.numbers header
  have outputAligned : (afterOmmerHeap header).toNat%8=0:=by rw [numbers.transactions]; have aligned:=physical.buffers.ommer.headerAligned; omega
  have separate : (afterOmmerHeap header).toNat+32≤2701134824 ∨ header.toNat+248≤(afterOmmerHeap header).toNat:=by
    right; rw [numbers.transactions]; omega
  obtain ⟨funded,child,returned,run⟩:=CallNormal.ignored_callee_return current target (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one args called normal
  obtain ⟨answer,domain,endian,code,heapCell,globals,memory⟩:=Mpt.CurrentIndexed.body_normal expanded roots (physical.data.keccak.of_frame rfl)
    inputBefore (by decide) outputAligned separate physical.frontier.afterHeader returned run
  have endpoint:=CallNormal.ignored_target current target (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one args called returned child run normal
  change child.globals.lookup (ofString "heap_ptr")=some (.val (.word entry.heap)) at heapCell
  rw [heapEq] at heapCell
  rw [endpoint]
  exact ⟨physical.of_heap_band domain endian code globals heapCell rfl memory,rfl⟩

/-- Main's literal first transaction-trie caller instantiates the complete
current builder allowance from its same decoded scan/header/startup evidence. -/
theorem PhysicalHeader.transaction_cost {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) (checked : RunAttempt.TransactionsNonempty input) :
    current.clock-(evaluateHOLFiniteState current transactionTrieCall).2.clock≤91390403933770583 := by
  obtain ⟨array,count,slices,callee,args,called,countEq,countBound,⟨entry⟩,roots⟩:=physical.transaction_entry_owned checked
  exact ClockCost.call_current current (some none) (ofString "build_mpt_indexed") transactionTrieArguments _ Mpt.Indexed.body callee .one 91390403933770582
    args called (Mpt.CurrentIndexed.uniform_body_cost entry roots (physical.data.keccak.of_frame rfl)
      (by
        have heapEq : entry.heap=headerFrontier header:=by
          simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using entry.heapCell.symm.trans physical.frontier.cell
        rw [heapEq]; have a:=physical.before; have b:=physical.frontier.afterHeader; omega)
      countBound (by decide))

/-- The whole actual payload-header execution through its transaction
trie either stops within the combined allowance or reaches its unchanged
withdrawal suffix with all original physical inputs. -/
theorem to_after_transaction {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary)
    (checked : RunAttempt.TransactionsNonempty input) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source PayloadHeader.body=(outcome,post)) :
    (source.clock-post.clock≤91390404330701644 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ header current inner encoded,PhysicalHeader input source current pointer si record gasWord boundary header ∧
        encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
        current.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤91390404330701644 ∧ CallPrefix.ScopeFrame post inner ∧
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
    change entered.clock-current.clock≤91390403933770583 at callPrice
    change current.clock≤entered.clock at callForward
    cases result with
    | none=>
      obtain ⟨retained,localsEq⟩:=physical.transaction_normal checked computed
      exact Or.inr ⟨header,current,inner,encoded,retained,encodedBound,withdrawalBound,number,
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

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.of_heap_band
