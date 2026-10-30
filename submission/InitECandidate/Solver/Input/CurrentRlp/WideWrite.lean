import InitECandidate.Solver.Input.CurrentRlp.BytesWrite
import InitECandidate.Solver.Input.RlpWrite.U256PutCall
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.CallPrefixGlobals
import InitECandidate.Solver.Input.CallPrefixNormalTrace
import InitECandidate.Solver.Input.GlobalEffectsScoped
import InitECandidate.Solver.Input.HeapScopeCost

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

namespace InitECandidate.Solver.Input.CurrentRlp.WideWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite.U256Put

/-- The real fresh scratch allocation bounds the minimum representation.
The destination needs no supplied mapping or ownership: failed byte writes
are included in the actual source-clock bound. -/
theorem suffix_current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (words : RlpWrite.U256Value.Words) (dst tmp : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (t : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (temporary : AllocatedBytes.Arena tmp 32) :
    source.clock-(evaluateHOLFiniteState source afterTemporary).2.clock≤131 := by
  by_cases funded : 68≤source.clock
  · have codes:=helper_codes source installed
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
        [localVar "v",localVar "tmp"]=some [RlpWrite.U256Value.tuple words,.val (.word tmp)]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v,t]
    have mapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (tmp+BitVec.ofNat 64 offset)):=by
      intro offset inside
      exact AllocatedBytes.byte_mapped source tmp 32 offset domain temporary inside
    obtain ⟨memory,length,paid,small,paidBound,run,frame⟩:=RlpWrite.U256Min.call_execute source words tmp "n"
      [localVar "v",localVar "tmp"] afterMinimum args codes.minCode codes.minCodes mapped funded
    let ready:=bind {source with memory:=memory,clock:=source.clock-1-paid} "n" (BitVec.ofNat 64 length)
    have dR : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
      (bind_lookup_other _ "n" "dst" _ (by decide)).trans d
    have tR : ready.locals.lookup (ofString "tmp")=some (.val (.word tmp)):=
      (bind_lookup_other _ "n" "tmp" _ (by decide)).trans t
    have nR : ready.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=bind_lookup_same _ _ _
    have byteArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query))
        [localVar "dst",localVar "tmp",localVar "n"]=some [.val (.word dst),.val (.word tmp),.val (.word (BitVec.ofNat 64 length))]:=by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dR,tR,nR]
    obtain ⟨callee,called,childD,childS,childN⟩:=RlpWrite.BytesWrite.environment ready.code.lookup dst tmp (BitVec.ofNat 64 length)
      (BytesWrite.original_code ready.code installed)
    have byteCost:=BytesWrite.body_known_length_cost (callEntryStateHOLFinite ready callee) dst tmp length (by omega)
      installed domain childD childS childN
    rw [BytesWrite.current_body] at byteCost
    have price : CopyAny.price length≤41:=by unfold CopyAny.price; omega
    have afterCost : ClockCost.Bound ready.code afterEncoded 1:=by
      exact ClockCost.sequence ready.code _ _ 1 0 (HeapScope.release_call_cost ready.code installed (some none) [localVar "mark"])
        (ClockCost.returned ready.code (localVar "w"))
    have bounded:=ClockCost.scoped_reached_current ready "w" .one (ofString "rlp_encode_bytes") _ _
      RlpWrite.BytesWrite.body afterEncoded callee .one 61 1 byteArgs called (by omega) (by
        intro target returned normal checked
        exact afterCost (CallNormal.continuationEntry ready target "w" returned)
          (Input.evaluation_fields (callEntryStateHOLFinite ready callee) target _ _ normal).2.2.2)
    rw [afterTemporary,run]
    change source.clock-(evaluateHOLFiniteState ready afterMinimum).2.clock≤131
    have clock : ready.clock=source.clock-1-paid:=rfl
    change ready.clock-(evaluateHOLFiniteState ready afterMinimum).2.clock≤61+1+1 at bounded
    have decreases:=evaluateHOLFiniteState_clock_le ready afterMinimum
    omega
  · omega

/-- Every current wide-writer outcome, without output ownership. The actual
failed allocator is charged; its successful path derives owned scratch. -/
theorem body_current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (words : RlpWrite.U256Value.Words) (dst heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤133 := by
  by_cases room : heap.toNat+32≤2952790016
  · by_cases funded : 2≤source.clock
    · have codes:=helper_codes source installed
      let ready:=prepared source heap
      have vR : ready.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words):=
        (prepared_other source heap "v" (by decide) (by decide)).trans v
      have dR : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
        (prepared_other source heap "dst" (by decide) (by decide)).trans d
      have temporary : AllocatedBytes.Arena heap 32:=⟨lower,by omega⟩
      have suffix:=suffix_current_cost ready words dst heap installed domain vR dR (prepared_locals source heap).1 temporary
      rw [current_body,prepare_execute source heap heapCell codes room funded]
      change source.clock-(evaluateHOLFiniteState ready afterTemporary).2.clock≤133
      have clock : ready.clock=source.clock-1-1:=rfl
      have decreases:=evaluateHOLFiniteState_clock_le ready afterTemporary
      omega
    · omega
  · have stopped:=no_room_cost source heap installed heapCell bounded room
    omega

end InitECandidate.Solver.Input.CurrentRlp.WideWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.suffix_current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.body_current_cost

namespace InitECandidate.Solver.Input.CurrentRlp.WideWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real normal minimum writer supplies its length and scratch-only frame
at the caller's actual clock. Its output mapping comes from fresh scratch. -/
theorem minimum_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (words : RlpWrite.U256Value.Words) (tmp : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "a")=some (RlpWrite.U256Value.tuple words))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word tmp)))
    (temporary : AllocatedBytes.Arena tmp 32) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source RlpWrite.U256Min.body=(some (.returned value),post)) :
    ∃ length,length≤32 ∧ value=.val (.word (BitVec.ofNat 64 length)) ∧
      MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      ∀ query,CopyGeneral.Away tmp query 32→post.memory query=source.memory query := by
  let padded:={source with clock:=source.clock+67}
  have codes:=helper_codes padded installed
  have mapped : ∀ offset<32,padded.memaddrs (panByteAlignHOL (width:=64) (tmp+BitVec.ofNat 64 offset)):=by
    intro offset inside
    exact AllocatedBytes.byte_mapped source tmp 32 offset domain temporary inside
  obtain ⟨target,length,paid,small,bounded,run,frame,memory⟩:=RlpWrite.U256Min.execute padded words tmp a outCell
    codes.minCodes.byteCode codes.minCodes.bitsCode codes.minCodes.bitCode codes.minCodes.limbCode mapped
    (by change 67≤source.clock+67; omega)
  have lifted:=panPropsEvaluateAddClockEq RlpWrite.U256Min.body source (some (.returned value)) post 67
    ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {post with clock:=post.clock+67}=target at endpoint
  have metadata:=congrArg MemoryMetadata.erase frame
  rw [←endpoint] at metadata memory
  refine ⟨length,small,answer,?_,?_⟩
  · exact metadata
  · intro query away
    exact memory query (fun offset inside=>(away offset inside).2)

end InitECandidate.Solver.Input.CurrentRlp.WideWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.minimum_current_normal

namespace InitECandidate.Solver.Input.CurrentRlp.WideWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite.U256Put

/-- Actual normal suffix: the owned minimum representation is at most32
bytes, and the weaker byte-writer contract supplies the output length/frame.
The real release restores the saved mark, independently of output mapping. -/
theorem suffix_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (words : RlpWrite.U256Value.Words) (dst tmp mark old query : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (t : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (m : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (temporary : AllocatedBytes.Arena tmp 32) (headerFits : dst.toNat+9<2^64)
    (aligned : floor%8=0) (belowDst : floor≤dst.toNat) (belowTmp : floor≤tmp.toNat) (earlier : query.toNat<floor)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterTemporary=(some (.returned value),post)) :
    ∃ encoded,1≤encoded ∧ encoded≤41 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      MemoryMetadata.erase post=MemoryMetadata.erase (HeapScope.releasePost source mark) ∧ post.memory query=source.memory query := by
  have codes:=helper_codes source installed
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address))
      [localVar "v",localVar "tmp"]=some [RlpWrite.U256Value.tuple words,.val (.word tmp)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,v,t]
  obtain ⟨callee,called,a,outCell⟩:=RlpWrite.U256Min.environment source.code.lookup words tmp codes.minCode
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "n" .one
    (ofString "u256_to_be_min") _ _ RlpWrite.U256Min.body afterMinimum callee .one args called value normal
  obtain ⟨length,small,answer,minFrame,minMemory⟩:=minimum_current_normal (callEntryStateHOLFinite source callee) child words tmp installed domain a outCell temporary returned run
  let ready:=CallNormal.continuationEntry source child "n" returned
  have metadataN : MemoryMetadata.erase ready=MemoryMetadata.erase source:=minFrame
  have currentInstalled : OriginalCode.Installed ready.code:=by rw [MemoryMetadata.code metadataN]; exact installed
  have currentDomain : ready.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain metadataN).trans domain
  have dN : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (CallNormal.continuation_lookup_other source child "n" "dst" returned (by decide)).trans d
  have tN : ready.locals.lookup (ofString "tmp")=some (.val (.word tmp)):=
    (CallNormal.continuation_lookup_other source child "n" "tmp" returned (by decide)).trans t
  have mN : ready.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (CallNormal.continuation_lookup_other source child "n" "mark" returned (by decide)).trans m
  have nN : ready.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=
    (CallNormal.continuation_lookup_same source child "n" returned).trans (congrArg some answer)
  have byteArgs : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address))
      [localVar "dst",localVar "tmp",localVar "n"]=some [.val (.word dst),.val (.word tmp),.val (.word (BitVec.ofNat 64 length))]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dN,tN,nN]
  obtain ⟨byteCallee,byteCalled,childD,childS,childN⟩:=RlpWrite.BytesWrite.environment ready.code.lookup dst tmp (BitVec.ofNat 64 length)
    (BytesWrite.original_code ready.code currentInstalled)
  obtain ⟨byteFunded,byteTarget,byteReturned,byteInner,byteRun,byteChecked,byteContinued,byteEndpoint⟩:=CallNormal.scoped_normal ready inner "w" .one
    (ofString "rlp_encode_bytes") _ _ RlpWrite.BytesWrite.body afterEncoded byteCallee .one byteArgs byteCalled value continued
  obtain ⟨encoded,positive,upper,uniform,byteAnswer,byteFrame,byteMemory⟩:=BytesWrite.body_current_normal
    (callEntryStateHOLFinite ready byteCallee) byteTarget dst tmp (BitVec.ofNat 64 length) query floor currentInstalled currentDomain
    childD childS childN headerFits aligned belowDst earlier byteReturned byteRun
  have countNumber : (BitVec.ofNat 64 length).toNat=length:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [countNumber] at upper
  let written:=CallNormal.continuationEntry ready byteTarget "w" byteReturned
  have metadataW : MemoryMetadata.erase written=MemoryMetadata.erase source:=byteFrame.trans metadataN
  have heapW : written.globals.lookup (ofString "heap_ptr")=some (.val (.word old)):=by
    have globals:=congrArg PanSemStateFiniteExact.globals metadataW
    change written.globals=source.globals at globals
    rw [globals]
    exact heapCell
  have mW : written.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (CallNormal.continuation_lookup_other ready byteTarget "w" "mark" byteReturned (by decide)).trans mN
  have wW : written.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=
    (CallNormal.continuation_lookup_same ready byteTarget "w" byteReturned).trans (congrArg some byteAnswer)
  have releaseArgs : evalListHOLFinite written (h:=fun address=>Classical.propDecidable (written.memaddrs address))
      [localVar "mark"]=some [.val (.word mark)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,mW]
  have ignored : LocalPrefix (ofString "_") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]):=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨released,releaseRun,returnRun⟩:=sequence_returned written byteInner _ _ value (ignored.summary_full written).2.1 byteContinued
  have releaseFunded:=(CallNormal.ignored_data written released (ofString "heap_release") [localVar "mark"] releaseRun).1
  have writtenInstalled : OriginalCode.Installed written.code:=by rw [MemoryMetadata.code metadataW]; exact installed
  have releaseExpected:=HeapScope.release_call_execute written mark old [localVar "mark"] releaseArgs heapW
    (HeapScope.release_original_code written.code writtenInstalled) releaseFunded
  have releasedEq : released=HeapScope.releasePost {written with clock:=written.clock-1} mark:=
    congrArg Prod.snd (releaseRun.symm.trans releaseExpected)
  have wReleased : released.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=by rw [releasedEq]; exact wW
  obtain ⟨read,innerEq⟩:=return_normal released byteInner (localVar "w") value returnRun
  have expectedRead : eval released (localVar "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=by
    simp [eval,evalHOLExact,toExact,localVar,wReleased]
  have valueEq : value=.val (.word (BitVec.ofNat 64 encoded)):=Option.some.inj (read.symm.trans expectedRead)
  have tmpFits : tmp.toNat+32<2^64:=by rcases temporary with ⟨lower,room⟩; omega
  have tmpAway:=CopyGeneral.Away.after_floor tmp query 32 floor aligned belowTmp tmpFits earlier
  have beforeMemory : written.memory query=source.memory query:=(byteMemory.trans (minMemory query tmpAway))
  refine ⟨encoded,positive,by omega,valueEq,?_,?_⟩
  · rw [endpoint,byteEndpoint,innerEq,releasedEq]
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
      {state with globals:=state.globals.update (ofString "heap_ptr",.val (.word mark))}) metadataW
  · rw [endpoint,byteEndpoint,innerEq,releasedEq]
    exact beforeMemory

end InitECandidate.Solver.Input.CurrentRlp.WideWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.suffix_current_normal

namespace InitECandidate.Solver.Input.CurrentRlp.WideWrite
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch RlpWrite.U256Put

/-- A genuine current normal wide write restores its own saved heap mark,
returns1..41encoded bytes and retains all words below output and scratch.
Only the actual fresh scratch allocation supplies ownership. -/
theorem body_current_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (words : RlpWrite.U256Value.Words) (dst heap query : BitVec 64) (floor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (v : source.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words))
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (lower : 2701131776≤heap.toNat) (bounded : heap.toNat≤2952790016)
    (headerFits : dst.toNat+9<2^64) (aligned : floor%8=0) (belowDst : floor≤dst.toNat)
    (belowHeap : floor≤heap.toNat) (earlier : query.toNat<floor)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ encoded,1≤encoded ∧ encoded≤41 ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      source.clock-post.clock≤133 ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧ post.memory query=source.memory query := by
  have room:=normal_room source post heap installed heapCell bounded value normal
  let padded:={source with clock:=source.clock+2}
  let ready:=prepared padded heap
  have vR : ready.locals.lookup (ofString "v")=some (RlpWrite.U256Value.tuple words):=
    (prepared_other padded heap "v" (by decide) (by decide)).trans v
  have dR : ready.locals.lookup (ofString "dst")=some (.val (.word dst)):=
    (prepared_other padded heap "dst" (by decide) (by decide)).trans d
  have temporary : AllocatedBytes.Arena heap 32:=⟨lower,by omega⟩
  have preparedRun:=prepare_execute padded heap heapCell (helper_codes padded installed) room (by change 2≤source.clock+2; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) post 2 ⟨normal,by intro impossible; cases impossible⟩
  have same:=preparedRun.symm.trans lifted
  let inner:=(evaluateHOLFiniteState ready afterTemporary).2
  have returnedEq : (evaluateHOLFiniteState ready afterTemporary).1=some (.returned value):=congrArg Prod.fst same
  have suffixRun : evaluateHOLFiniteState ready afterTemporary=(some (.returned value),inner):=by
    apply Prod.ext
    · exact returnedEq
    · rfl
  obtain ⟨encoded,positive,small,answer,frame,memory⟩:=suffix_current_normal ready inner words dst heap heap
    (PersistentAlloc.rounded heap 32#64) query floor installed domain vR dR (prepared_locals padded heap).1 (prepared_locals padded heap).2
    (prepared_heap padded heap) temporary headerFits aligned belowDst belowHeap earlier value suffixRun
  have endpoint:=congrArg Prod.snd same
  have metadataEndpoint:=congrArg MemoryMetadata.erase endpoint
  have releasedState : MemoryMetadata.erase (HeapScope.releasePost ready heap)=MemoryMetadata.erase source:=by
    change MemoryMetadata.erase {source with
      globals:=(source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 32#64)))).update (ofString "heap_ptr",.val (.word heap))}=
      MemoryMetadata.erase source
    rw [restore_global source.globals (ofString "heap_ptr") (.val (.word heap)) _ heapCell]
  have metadata : MemoryMetadata.erase post=MemoryMetadata.erase source:=metadataEndpoint.symm.trans (frame.trans releasedState)
  have cost:=body_current_cost source words dst heap installed domain v d heapCell lower bounded
  rw [normal] at cost
  refine ⟨encoded,positive,small,answer,cost,metadata,?_⟩
  have memoryEndpoint:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>state.memory query) endpoint
  exact memoryEndpoint.symm.trans memory

end InitECandidate.Solver.Input.CurrentRlp.WideWrite

#print axioms InitECandidate.Solver.Input.CurrentRlp.WideWrite.body_current_normal
