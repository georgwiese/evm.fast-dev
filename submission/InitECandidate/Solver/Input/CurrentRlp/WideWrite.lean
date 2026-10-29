import InitECandidate.Solver.Input.CurrentRlp.BytesWrite
import InitECandidate.Solver.Input.RlpWrite.U256PutCall
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixGlobals
import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.GlobalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentRlp.WideWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 100000

macro "current_entry" : tactic => `(tactic| simp only [Code.entry,Code.declaration,Code.body,GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,
    Guest.Software.guestFn_rlp_put_u256,Guest.Software.guestFn_heap_mark,Guest.Software.guestFn_heap_release,
    Guest.Software.guestFn_u256_to_be_min,Guest.Software.guestFn_u256_byte_length,Guest.Software.guestFn_u256_bit_length,
    Guest.Software.guestFn_bit_length64,Guest.Software.guestFn_u256_limb,
    RlpWrite.U256Put.formals,RlpWrite.U256Put.body,Guest.guestFn_rlp_put_u256,
    HeapScope.markBody,HeapScope.releaseFormals,HeapScope.releaseBody,
    RlpWrite.U256Min.formals,RlpWrite.U256Min.body,Guest.guestFn_u256_to_be_min,
    RlpWrite.U256ByteLength.formals,RlpWrite.U256ByteLength.body,Guest.guestFn_u256_byte_length,
    RlpWrite.U256Bits.formals,RlpWrite.U256Bits.body,Guest.guestFn_u256_bit_length,
    RlpWrite.BitLength.formals,RlpWrite.BitLength.body,Guest.guestFn_bit_length64,
    RlpWrite.U256Limb.formals,RlpWrite.U256Limb.body,Guest.guestFn_u256_limb,
    RlpWrite.U256Value.tupleShape,paramToHOL,shapeToHOL,List.map_cons,List.map_nil])

abbrev body:=Code.body .writeWide

theorem current_body : body=RlpWrite.U256Put.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_put_u256")=some (RlpWrite.U256Put.formals,body,.one) := by
  apply Code.installed_as code installed .writeWide
  current_entry

/-- All helpers are the actual current software entries. In particular,
the wide writer calls the genuine bounded allocator and software byte writer. -/
theorem helper_codes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) : RlpWrite.U256Put.Codes source := by
  refine ⟨?_,PersistentAlloc.original_code source.code installed,?_,?_,?_,BytesWrite.helper_codes source installed,?_⟩
  · apply Code.installed_as source.code installed .heapMark; current_entry
  · apply Code.installed_as source.code installed .wideMin; current_entry
  · refine ⟨?_,?_,?_,?_⟩
    · apply Code.installed_as source.code installed .wideBytes; current_entry
    · apply Code.installed_as source.code installed .wideBits; current_entry
    · apply Code.installed_as source.code installed .bitLength; current_entry
    · apply Code.installed_as source.code installed .limb; current_entry
  · simpa only [BytesWrite.current_body] using BytesWrite.original_code source.code installed
  · apply Code.installed_as source.code installed .heapRelease; current_entry

structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst heap : BitVec 64) : Prop where
  metadata : MemoryMetadata.erase target=MemoryMetadata.erase source
  memory : ∀ query,CopyGeneral.Away dst query 41→CopyGeneral.Away heap query 32→target.memory query=source.memory query

/-- Genuine current wide writing with its real persistent request room.
The caller's earlier physical buffer supplies output mapping; normality is
not assumed to obtain the run or encoded-size and memory conclusions. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : RlpWrite.U256Value.Words) (dst heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (room : heap.toNat+32≤2952790016)
    (dstArena : AllocatedBytes.Arena dst 41) (funded : 124≤source.clock) :
    ∃ target encoded paid,1≤encoded ∧ encoded≤41 ∧ paid≤124 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      evaluateHOLFiniteState source body=(some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      target.clock=source.clock-paid ∧ Frame source target dst heap := by
  obtain ⟨target,encoded,paid,positive,upper,bound,number,run,frame,memory⟩:=RlpWrite.U256Put.execute source words dst heap v d heapCell
    (helper_codes source installed) domain lower room dstArena funded
  have clock:=congrArg PanSemStateFiniteExact.clock frame
  change target.clock=source.clock-paid at clock
  have metadata:=congrArg MemoryMetadata.erase frame
  exact ⟨target,encoded,paid,positive,upper,bound,number,run,clock,metadata,
    fun query outAway tmpAway=>memory query outAway (fun offset inside=>(tmpAway offset inside).2)⟩

/-- An exhausted persistent request stops before either encoding child.
The first two actual calls therefore consume at most three source ticks. -/
theorem no_room_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (noRoom : ¬heap.toNat+32≤2952790016) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤3 := by
  by_cases zero : source.clock=0
  · omega
  have codes:=helper_codes source installed
  have markRun:=HeapScope.mark_call_execute source heap "mark" RlpWrite.U256Put.afterMark heapCell codes.markCode (by omega)
  let marked:=RlpWrite.U256Put.marked source heap
  have args : evalListHOLFinite marked (h:=fun address=>Classical.propDecidable (marked.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=rfl
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment marked.code.lookup 32#64 (PersistentAlloc.original_code marked.code installed)
  have price : marked.clock-(evaluateHOLFiniteState marked RlpWrite.U256Put.afterMark).2.clock≤2 := by
    rw [RlpWrite.U256Put.afterMark]
    apply ClockCost.scoped_reached_current marked "tmp" .one (ofString "alloc") [.const 32#64] _ PersistentAlloc.body RlpWrite.U256Put.afterTemporary callee .one 1 0 args called
      (PersistentAlloc.body_price marked.code installed (callEntryStateHOLFinite marked callee) rfl)
    intro target returned normal checked
    have room:=PersistentAlloc.room_of_normal (callEntryStateHOLFinite marked callee) target heap 32#64 amountCell heapCell bounded
      (Trap.original_code source.code installed) returned normal
    exact (noRoom room).elim
  rw [current_body,RlpWrite.U256Put.body_shape,markRun]
  change source.clock-(evaluateHOLFiniteState marked RlpWrite.U256Put.afterMark).2.clock≤3
  have clock : marked.clock=source.clock-1:=rfl
  omega

/-- Every actual wide-writer outcome is covered. A failed request uses the
cheap stopping prefix; successful-room entries use their owned fresh spans. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : RlpWrite.U256Value.Words) (dst heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016) (dstArena : AllocatedBytes.Arena dst 41) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤124 := by
  by_cases room : heap.toNat+32≤2952790016
  · by_cases funded : 124≤source.clock
    · obtain ⟨target,encoded,paid,positive,upper,bound,number,run,clock,frame⟩:=execute source words dst heap installed domain v d heapCell lower room dstArena funded
      rw [run]
      change source.clock-target.clock≤124
      omega
    · omega
  · have stopped:=no_room_cost source heap installed heapCell bounded room
    omega


def allocationActions : List CallPrefix.Action:=[
  .scoped (ofString "mark") .one (ofString "heap_mark") [],
  .scoped (ofString "tmp") .one (ofString "alloc") [.const 32#64]]

theorem body_allocations : body=CallPrefix.program allocationActions RlpWrite.U256Put.afterTemporary := by
  rw [current_body,RlpWrite.U256Put.body_shape]
  rfl

/-- A real normal wide-writer execution necessarily passed its own actual
allocation. The persistent request room is a conclusion, not a caller axiom. -/
theorem normal_room (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (bounded : heap.toNat≤2952790016)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) : heap.toNat+32≤2952790016 := by
  have codes:=helper_codes source installed
  rw [body_allocations] at normal
  have never : NoReturn.Never (CallPrefix.program allocationActions .skip):=
    NoReturn.scoped_call _ _ _ _ _ (NoReturn.scoped_call _ _ _ _ _ NoReturn.skip)
  obtain ⟨current,inner,execution,endpoint,remaining⟩:=CallPrefix.normal_trace source post allocationActions RlpWrite.U256Put.afterTemporary value never normal
  obtain ⟨middle,first,next⟩ : ∃ middle,
      CallPrefix.Reaches source (.scoped (ofString "mark") .one (ofString "heap_mark") []) middle ∧
      CallPrefix.Execution middle [.scoped (ofString "tmp") .one (ofString "alloc") [.const 32#64]] current:=by
    cases execution with
    | step first next=>exact ⟨_,first,next⟩
  have preserved : GlobalEffects.Preserves (ofString "heap_ptr") source.code
      (CallPrefix.program [.scoped (ofString "mark") .one (ofString "heap_mark") []] .skip):=by
    apply GlobalEffects.scoped_body _ source.code _ _ _ _ _ [] HeapScope.markBody .one codes.markCode
    · rw [HeapScope.mark_shape]
      exact GlobalEffects.returned _ _ _
    · exact GlobalEffects.skip _ _
  have middleHeap:=(first.globals (ofString "heap_ptr") preserved).trans heapCell
  have middleInstalled : OriginalCode.Installed middle.code:=by rw [first.runtime.2.2.2.1]; exact installed
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=rfl
  exact (CallPrefix.Execution.alloc_next (source:=middle) (target:=current) (ofString "tmp") [.const 32#64] heap 32#64 []
    middleInstalled args middleHeap bounded next).1

/-- Normality supplies the writer's own request room; padding then recovers
the same actual output size and complete two-span memory frame at any clock. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (words : RlpWrite.U256Value.Words) (dst heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016) (dstArena : AllocatedBytes.Arena dst 41)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ encoded,1≤encoded ∧ encoded≤41 ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-target.clock≤124 ∧ Frame source target dst heap := by
  have room:=normal_room source target heap installed heapCell bounded value normal
  let padded:={source with clock:=source.clock+124}
  obtain ⟨post,encoded,paid,positive,upper,bound,number,run,clock,frame⟩:=execute padded words dst heap installed domain v d heapCell lower room dstArena
    (by change 124≤source.clock+124; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target 124 ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+124}=post at endpoint
  rw [←endpoint] at frame
  have cost:=body_cost source words dst heap installed domain v d heapCell lower bounded dstArena
  rw [normal] at cost
  exact ⟨encoded,positive,upper,number,answer,cost,frame.metadata,frame.memory⟩

end InitECandidate.Solver.Input.CurrentRlp.WideWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.original_code
#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.helper_codes
#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.execute
#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.no_room_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.body_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.body_allocations

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.normal_room

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.body_normal
