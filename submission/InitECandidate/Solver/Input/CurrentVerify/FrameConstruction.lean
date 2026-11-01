import InitECandidate.Solver.Input.CurrentVerify.FreshTransactionMemory
import InitECandidate.Solver.GasBudget.FrameNewFreshFields
import InitECandidate.Solver.ScratchList.Call
import InitECandidate.Solver.JumpDest.Call
import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.Arenas.DownPlan

namespace InitECandidate.Solver.Input.CurrentVerify.FrameConstruction
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def logsBody : ProgHOL 64 := match Guest.Software.guestFn_lst_new_scratch with | .function fn=>progToHOL fn.body | _=>.skip
abbrev logsFormals : List (MlS×ShapeHOL) := [(ofString "esz",.one),(ofString "cap",.one)]
def tableBody : ProgHOL 64 := match Guest.Software.guestFn_htab_new_scratch with | .function fn=>progToHOL fn.body | _=>.skip
abbrev tableFormals : List (MlS×ShapeHOL) := [(ofString "key_len",.one),(ofString "cap",.one)]
def countBody : ProgHOL 64 := match Guest.Software.guestFn_htab_count with | .function fn=>progToHOL fn.body | _=>.skip
abbrev countFormals : List (MlS×ShapeHOL) := [(ofString "t",.one)]

abbrev body := GasBudget.FrameNew.body
abbrev formals : List (MlS×ShapeHOL):=[(ofString "msg",.one)]

/-- Kernel-checked equality to the installed current Software body, rather
than an assumption that the legacy frame proof describes today's program. -/
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "frame_new")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 423
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_frame_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, GasBudget.FrameNew.body, formals, Guest.Software.guestFn_frame_new, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem scratch_mark_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "scratch_mark")=some ([],Arenas.markBody .down,.one) := by
  have checked := OriginalCode.indexed code installed 9
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_scratch_mark) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Arenas.markBody, Guest.Software.guestFn_scratch_mark, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem memory_mark_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "frame_mem_mark")=some ([],Arenas.markBody .up,.one) := by
  have checked := OriginalCode.indexed code installed 6
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_frame_mem_mark) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Arenas.markBody, Guest.Software.guestFn_frame_mem_mark, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem jump_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "compute_jumpdests")=some (JumpDest.formals,JumpDest.body,.one) := by
  have checked := OriginalCode.indexed code installed 419
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_compute_jumpdests) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, JumpDest.formals, JumpDest.body, Guest.Software.guestFn_compute_jumpdests, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem logs_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "lst_new_scratch")=some (logsFormals,logsBody,.one) := by
  have checked := OriginalCode.indexed code installed 370
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_lst_new_scratch) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, logsFormals, logsBody, Guest.Software.guestFn_lst_new_scratch, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem table_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_new_scratch")=some (tableFormals,tableBody,.one) := by
  have checked := OriginalCode.indexed code installed 117
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_new_scratch) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, tableFormals, tableBody, Guest.Software.guestFn_htab_new_scratch, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem count_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_count")=some (countFormals,countBody,.one) := by
  have checked := OriginalCode.indexed code installed 129
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_count) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, countFormals, countBody, Guest.Software.guestFn_htab_count, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem constructor_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    GasBudget.FrameNew.Code source :=
  ⟨scratch_mark_code source.code installed,memory_mark_code source.code installed,
    by simpa only [Arenas.functionName] using Arenas.original_code source.code installed .down,
    Zero.original_code source.code installed⟩

/-- The current Patricia constructor has four allocations and no clearing
loop. The bound covers failure/trap outcomes and needs no assumed arena room. -/
theorem table_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code tableBody 8 := by
  apply ClockCost.mono code _ _ 8
  · simp only [tableBody,Guest.Software.guestFn_htab_new_scratch,progToHOL,expToHOL,shapeToHOL,
      List.map_cons,List.map_nil,Option.map_none,Option.map_some]
    repeat' first
      | apply ClockCost.sequence
      | apply ClockCost.conditional
      | apply ClockCost.declared
      | apply Arenas.scoped_price code installed .down
      | exact ClockCost.store code _ _
      | exact ClockCost.assign code _ _
      | exact ClockCost.skip code
      | exact ClockCost.returned code _
  · decide

theorem logs_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code logsBody 4 := by
  apply ClockCost.mono code _ _ 4
  · simp only [logsBody,Guest.Software.guestFn_lst_new_scratch,progToHOL,expToHOL,shapeToHOL,
      List.map_cons,List.map_nil,Option.map_none,Option.map_some]
    repeat' first
      | apply ClockCost.sequence
      | apply Arenas.scoped_price code installed .down
      | exact ClockCost.store code _ _
      | exact ClockCost.returned code _
  · decide

theorem count_price (code) : ClockCost.Bound code countBody 0 := by
  simp only [countBody,Guest.Software.guestFn_htab_count,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil]
  exact ClockCost.returned code _

def afterJump : ProgHOL 64 := match GasBudget.FrameNew.afterGas with | .decCall _ _ _ _ rest=>rest | _=>.skip

/-- Complete current frame_new tail following bitmap construction, including
both constructors, both count calls and every store through the real return. -/
theorem after_jump_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterJump 16 := by
  apply ClockCost.mono code _ _ 16
  · simp only [afterJump,GasBudget.FrameNew.afterGas,GasBudget.FrameNew.gasSite,
      GasBudget.FrameNew.afterZero,GasBudget.FrameNew.body,Guest.Software.guestFn_frame_new,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
    repeat' first
      | apply ClockCost.sequence
      | apply ClockCost.scoped_body code _ _ _ _ _ logsFormals logsBody .one 4 _ (logs_code code installed) (logs_price code installed)
      | apply ClockCost.scoped_body code _ _ _ _ _ tableFormals tableBody .one 8 _ (table_code code installed) (table_price code installed)
      | apply ClockCost.scoped_body code _ _ _ _ _ countFormals countBody .one 0 _ (count_code code installed) (count_price code)
      | exact ClockCost.call_body code (some (some (ofString "acc_n"))) (ofString "htab_count") _ countFormals countBody .one 0 (count_code code installed) (count_price code)
      | exact ClockCost.store code _ _
      | exact ClockCost.returned code _
  · decide

/-- All message and table headers are genuinely below the persistent
allocator's cap, hence below the initial frame-memory allocation region. -/
theorem memory_layout {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage) :
    message.toNat+176≤accounts.toNat ∧ accounts.toNat+88≤storage.toNat ∧ storage.toNat+88≤2952790016 := by
  obtain ⟨cursor,cell,lower,upper,aligned⟩:=state.heap
  have first:=state.accountsImage.geometry.header_before_end
  have second:=state.storageImage.geometry.header_before_end
  have order:=state.afterAccounts
  exact ⟨state.afterMessage,by omega,by omega⟩


/-- The genuine bitmap execution gives an all-clock cost: a short caller
already has fewer ticks than the allowance, while a funded caller executes the
proved scan. No successful callee run is assumed. -/
theorem jump_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower pointer bytes : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (scratchCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (lowerCell : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (pointerCell : source.locals.lookup (ofString "code")=some (.val (.word pointer)))
    (bytesCell : source.locals.lookup (ofString "n")=some (.val (.word bytes)))
    (aligned : lower.toNat%8=0) (fits : bytes.toNat+63<2^64)
    (room : lower.toNat+JumpDest.bitmapBytes bytes.toNat≤scratch.toNat)
    (codeMapped : ∀ offset<bytes.toNat,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress pointer offset)))
    (bitmapMapped : ∀ offset,offset+8≤JumpDest.bitmapBytes bytes.toNat → offset%8=0 →
      source.memaddrs (byteAddress (Arenas.rounded .down scratch (JumpDest.bytesWord bytes)) offset)) :
    source.clock-(evaluateHOLFiniteState source JumpDest.body).2.clock≤bytes.toNat+Zero.price (JumpDest.bitmapBytes bytes.toNat)+2 := by
  by_cases short : source.clock≤bytes.toNat+Zero.price (JumpDest.bitmapBytes bytes.toNat)+2
  · omega
  · obtain ⟨post,spent,bound,run,frame,preserved⟩:=JumpDest.execute source scratch lower pointer bytes
      (Arenas.original_code source.code installed .down) (Zero.original_code source.code installed)
      scratchCell lowerCell pointerCell bytesCell aligned fits room codeMapped bitmapMapped (by omega)
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change post.clock=source.clock-(Zero.price (JumpDest.bitmapBytes bytes.toNat)+2+spent) at clock
    rw [run]
    change source.clock-post.clock≤_
    omega

abbrev scratchStart : BitVec 64:=2965299200#64
abbrev memoryStart : BitVec 64:=2952790016#64
abbrev frameStart : BitVec 64:=2965298920#64
abbrev stackStart : BitVec 64:=2965297896#64
abbrev memoryNext : BitVec 64:=2952791040#64

/-- This prefix writes only within the newly allocated frame. -/
theorem fresh_memory_before (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (words : GasBudget.FrameNew.MessageWords) (query : BitVec 64) (before : query.toNat<frameStart.toNat) :
    (GasBudget.FrameNew.fresh source scratchStart memoryStart words).memory query=source.memory query := by
  have away : ∀ offset<GasBudget.FrameNew.size,query≠byteAddress frameStart offset := by
    intro offset inside equal
    have number:=byteAddress_toNat frameStart offset (by change offset<280 at inside; change 2965298920+offset<2^64; omega)
    rw [←equal] at number
    change query.toNat=2965298920+offset at number
    change query.toNat<2965298920 at before
    omega
  change WordWrites.write
    (GasBudget.FrameNew.memoryAllocated (GasBudget.FrameNew.zeroed source scratchStart memoryStart) frameStart memoryStart scratchStart).memory
    (FieldStores.writes frameStart (GasBudget.FrameNew.fields memoryStart memoryStart words)) query=source.memory query
  rw [WordWrites.write_away]
  · rw [GasBudget.FrameNew.allocation_memory_away]
    · exact GasBudget.FrameNew.zeroed_away source scratchStart memoryStart query away
    · simp only [FieldStores.writes,GasBudget.FrameNew.stackFields,List.map_cons,List.map_nil,
        List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨away 208 (by decide),away 8 (by decide),away 232 (by decide)⟩
  · simp only [FieldStores.writes,GasBudget.FrameNew.fields,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨away 224 (by decide),away 24 (by decide),away 40 (by decide),away 48 (by decide),
      away 56 (by decide),away 64 (by decide),away 72 (by decide)⟩

/-- The real message supplies all operands for the complete17-tick frame
initialization. In particular, ownership and separation are derived here. -/
theorem actual_prefix {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (messageCell : source.locals.lookup (ofString "msg")=some (.val (.word message)))
    (enough : 17≤source.clock) :
    ∃ words : GasBudget.FrameNew.MessageWords,
      words.gas=30000000#64 ∧ words.reservoir=1566720#64 ∧ words.length.toNat≤65536 ∧ (words.length=0#64 ∨ AllocatedBytes.Arena words.code words.length.toNat) ∧
      source.memory (message+112#64)=.word words.code ∧ source.memory (message+120#64)=.word words.length ∧
      evaluateHOLFiniteState source body=
        (let output:=evaluateHOLFiniteState (GasBudget.FrameNew.fresh source scratchStart memoryStart words) GasBudget.FrameNew.afterGas
         (output.1,GasBudget.FrameNew.freshRestore source scratchStart memoryStart output.2)) := by
  obtain ⟨pointer,bytes,pointerCell,bytesCell,bound,arena⟩:=state.words.code
  let words : GasBudget.FrameNew.MessageWords:=⟨pointer,bytes,30000000#64,1566720#64⟩
  have messageBound : message.toNat+176≤memoryStart.toNat := by
    obtain ⟨first,second,third⟩:=memory_layout state
    change message.toNat+176≤2952790016
    omega
  have maps : ∀ offset∈GasBudget.FrameNew.messageOffsets,source.memaddrs (message+BitVec.ofNat 64 offset) := by
    intro offset member
    have inside : offset<176 := by
      simp only [GasBudget.FrameNew.messageOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    have aligned : offset%8=0 := by
      simp only [GasBudget.FrameNew.messageOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    exact AllocatedBytes.word_mapped source message 176 offset state.environment.arena.domain state.messageArena inside state.messageAligned aligned
  have cells : ∀ offset∈GasBudget.FrameNew.messageOffsets,
      source.memory (message+BitVec.ofNat 64 offset)=.word (words.atOffset offset) := by
    intro offset member
    simp only [GasBudget.FrameNew.messageOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact pointerCell
    · exact bytesCell
    · exact state.words.gas
    · exact state.words.stateGas
  have separation : ∀ readOffset∈GasBudget.FrameNew.messageOffsets,∀ writeOffset<GasBudget.FrameNew.size,
      message+BitVec.ofNat 64 readOffset≠byteAddress frameStart writeOffset := by
    intro readOffset member writeOffset inside equal
    have small : readOffset<176 := by
      simp only [GasBudget.FrameNew.messageOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    have readNumber : (message+BitVec.ofNat 64 readOffset).toNat=message.toNat+readOffset :=
      byteAddress_toNat message readOffset (by change message.toNat+176≤2952790016 at messageBound; omega)
    have writeNumber:=byteAddress_toNat frameStart writeOffset
      (by change writeOffset<280 at inside; change 2965298920+writeOffset<2^64; omega)
    have same:=congrArg BitVec.toNat equal
    rw [readNumber,writeNumber] at same
    change message.toNat+readOffset=2965298920+writeOffset at same
    change message.toNat+176≤2952790016 at messageBound
    omega
  have frameMapped : ∀ offset,offset+8≤GasBudget.FrameNew.size → offset%8=0 → source.memaddrs (byteAddress frameStart offset) := by
    intro offset inside aligned
    exact AllocatedBytes.word_mapped source frameStart 280 offset state.environment.arena.domain
      ⟨by decide,by decide⟩ (by change offset+8≤280 at inside; omega) (by decide) aligned
  have run:=GasBudget.FrameNew.fresh_execute source scratchStart memoryStart message words
    (constructor_code source state.environment.arena.code)
    (Arenas.original_code source.code state.environment.arena.code .up)
    state.environment.arena.scratch state.environment.arena.frame messageCell (by decide) (by decide) (by decide)
    frameMapped maps cells separation enough GasBudget.FrameNew.afterGas
  refine ⟨words,rfl,rfl,bound,arena,pointerCell,bytesCell,?_⟩
  change evaluateHOLFiniteState source GasBudget.FrameNew.body=_
  rw [GasBudget.FrameNew.actual_fresh_prefix]
  exact run

abbrev bodyPrice : Nat:=65830

theorem bitmap_bound {bytes : Nat} (bound : bytes≤65536) : JumpDest.bitmapBytes bytes≤8200 := by
  unfold JumpDest.bitmapBytes
  omega

theorem body_price_bound {bytes : BitVec 64} (bound : bytes.toNat≤65536) :
    bytes.toNat+Zero.price (JumpDest.bitmapBytes bytes.toNat)+37≤bodyPrice := by
  unfold Zero.price JumpDest.bitmapBytes bodyPrice
  omega


def jumpArguments : List (ExpHOL 64):=
  [.load .one (addConst (localVar "msg") 112#64),.load .one (addConst (localVar "msg") 120#64)]

theorem jump_shape : GasBudget.FrameNew.afterGas=.decCall (ofString "jd") .one (ofString "compute_jumpdests") jumpArguments afterJump := by
  simp only [afterJump,GasBudget.FrameNew.afterGas,GasBudget.FrameNew.gasSite,
    GasBudget.FrameNew.afterZero,GasBudget.FrameNew.body,Guest.Software.guestFn_frame_new,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    jumpArguments,addConst,localVar]

/-- Complete current frame_new source-clock cost at the genuinely constructed
message entry. Every physical premise comes from that entry; constructor and
count failures are covered by the universal tail cost. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (messageCell : source.locals.lookup (ofString "msg")=some (.val (.word message))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice := by
  by_cases short : source.clock≤bodyPrice
  · omega
  · obtain ⟨words,_,_,bound,codeArena,pointerCell,bytesCell,prefixRun⟩:=actual_prefix state messageCell (by unfold bodyPrice at short; omega)
    let fresh:=GasBudget.FrameNew.fresh source scratchStart memoryStart words
    have freshClock : fresh.clock=source.clock-17 := (GasBudget.FrameNew.fresh_budget source scratchStart memoryStart words).2
    have installed : OriginalCode.Installed fresh.code:=state.environment.arena.code
    have domain : fresh.memaddrs=InitE.ordinaryDomain:=state.environment.arena.domain
    have scratchCell : fresh.globals.lookup (ofString "scratch_ptr")=some (.val (.word stackStart)) := by
      simp [fresh,GasBudget.FrameNew.fresh,GasBudget.FrameNew.initialized,GasBudget.FrameNew.memoryAllocated,
        GasBudget.FrameNew.stackInitialized,GasBudget.FrameNew.stackAllocated,GasBudget.FrameNew.zeroed,
        GasBudget.FrameNew.allocated,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
      decide
    have lowerCell : fresh.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word memoryNext)) := by
      simp [fresh,GasBudget.FrameNew.fresh,GasBudget.FrameNew.initialized,GasBudget.FrameNew.memoryAllocated,
        Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
      decide
    have messageFresh : fresh.locals.lookup (ofString "msg")=some (.val (.word message)) := by
      simpa [fresh,GasBudget.FrameNew.fresh,GasBudget.FrameNew.initialized,GasBudget.FrameNew.memoryAllocated,
        GasBudget.FrameNew.stackInitialized,GasBudget.FrameNew.stackAllocated,GasBudget.FrameNew.zeroed,
        GasBudget.FrameNew.allocated,GasBudget.FrameNew.markedMemory,GasBudget.FrameNew.markedScratch,
        Arenas.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using messageCell
    have msgBefore : message.toNat+176≤2952790016 := by
      obtain ⟨first,second,third⟩:=memory_layout state
      omega
    have retained112 : fresh.memory (message+112#64)=.word words.code := by
      rw [fresh_memory_before]
      · exact pointerCell
      · have number : (message+112#64).toNat=message.toNat+112:=byteAddress_toNat message 112 (by omega)
        rw [number]; change message.toNat+112<2965298920; omega
    have retained120 : fresh.memory (message+120#64)=.word words.length := by
      rw [fresh_memory_before]
      · exact bytesCell
      · have number : (message+120#64).toNat=message.toNat+120:=byteAddress_toNat message 120 (by omega)
        rw [number]; change message.toNat+120<2965298920; omega
    have mapped112 : fresh.memaddrs (message+112#64):=
      AllocatedBytes.word_mapped fresh message 176 112 domain state.messageArena (by decide) state.messageAligned (by decide)
    have mapped120 : fresh.memaddrs (message+120#64):=
      AllocatedBytes.word_mapped fresh message 176 120 domain state.messageArena (by decide) state.messageAligned (by decide)
    have args : evalListHOLFinite fresh (h:=fun address=>Classical.propDecidable (fresh.memaddrs address)) jumpArguments=
        some (JumpDest.values words.code words.length) := by
      simp [jumpArguments,JumpDest.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,addConst,
        messageFresh,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped112,mapped120,retained112,retained120]
    obtain ⟨callee,called,codeLocal,lengthLocal⟩:=JumpDest.environment fresh.code.lookup words.code words.length (jump_code fresh.code installed)
    let entry:=callEntryStateHOLFinite fresh callee
    have bitmapBound:=bitmap_bound bound
    have fits : words.length.toNat+63<2^64 := by omega
    have number:=JumpDest.bytes_number words.length fits
    have room : memoryNext.toNat+JumpDest.bitmapBytes words.length.toNat≤stackStart.toNat := by
      change 2952791040+JumpDest.bitmapBytes words.length.toNat≤2965297896
      omega
    have roomWord : memoryNext.toNat+(JumpDest.bytesWord words.length).toNat≤stackStart.toNat := by rw [number]; exact room
    have geometry:=Arenas.downward_guards stackStart memoryNext (JumpDest.bytesWord words.length) (by decide) roomWord
    have bitmapArena : AllocatedBytes.Arena (Arenas.rounded .down stackStart (JumpDest.bytesWord words.length)) (JumpDest.bitmapBytes words.length.toNat) := by
      have lower:=geometry.2.2.1
      have upper:=geometry.2.2.2.1
      rw [number] at upper
      constructor
      · change 2952791040≤_ at lower; omega
      · change _≤2965297896 at upper; omega
    have codeMapped : ∀ offset<words.length.toNat,entry.memaddrs (panByteAlignHOL (width:=64) (byteAddress words.code offset)) := by
      intro offset inside
      rcases codeArena with zero|arena
      · rw [zero] at inside; change offset<0 at inside; omega
      · exact AllocatedBytes.byte_mapped entry words.code words.length.toNat offset domain arena inside
    have bitmapMapped : ∀ offset,offset+8≤JumpDest.bitmapBytes words.length.toNat → offset%8=0 →
        entry.memaddrs (byteAddress (Arenas.rounded .down stackStart (JumpDest.bytesWord words.length)) offset) := by
      intro offset inside aligned
      exact AllocatedBytes.word_mapped entry _ _ offset domain bitmapArena (by omega) geometry.2.2.2.2.2 aligned
    have scanCost:=jump_price entry stackStart memoryNext words.code words.length installed scratchCell lowerCell
      codeLocal lengthLocal (by decide) fits room codeMapped bitmapMapped
    have suffixCost:=ClockCost.scoped_current fresh (ofString "jd") .one (ofString "compute_jumpdests") jumpArguments
      (JumpDest.values words.code words.length) JumpDest.body afterJump callee .one
      (words.length.toNat+Zero.price (JumpDest.bitmapBytes words.length.toNat)+2) 16 args called scanCost (after_jump_price fresh.code installed)
    rw [←jump_shape] at suffixCost
    have forward:=evaluateHOLFiniteState_clock_le fresh GasBudget.FrameNew.afterGas
    have boundTotal:=body_price_bound bound
    have equality:=congrArg (fun result=>result.2.clock) prefixRun
    change (evaluateHOLFiniteState source body).2.clock=(evaluateHOLFiniteState fresh GasBudget.FrameNew.afterGas).2.clock at equality
    rw [equality]
    change fresh.clock-(evaluateHOLFiniteState fresh GasBudget.FrameNew.afterGas).2.clock≤_ at suffixCost
    unfold bodyPrice at short boundTotal ⊢
    omega

end InitECandidate.Solver.Input.CurrentVerify.FrameConstruction

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.scratch_mark_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.memory_mark_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.jump_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.logs_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.table_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.count_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.constructor_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.table_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.logs_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.count_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.after_jump_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.jump_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.fresh_memory_before
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.actual_prefix
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.bitmap_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.body_price_bound
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.memory_layout

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.jump_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameConstruction.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.FrameOpening
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64:=match Guest.Software.guestFn_frame_open with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "msg",.one),(ofString "kind",.one)]
def values (message kind : BitVec 64) : List (ValueHOL 64):=[.val (.word message),.val (.word kind)]
def rawLocals (message kind : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "kind" then some (.val (.word kind)) else if name=ofString "msg" then some (.val (.word message)) else none

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "frame_open")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 530
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_frame_open) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_frame_open,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem environment (code : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (message kind : BitVec 64) (known : code (ofString "frame_open")=some (formals,body,.one)) :
    ∃ callee,lookupCodeHOLFinite code (ofString "frame_open") (values message kind)=some (body,callee,.one) ∧
      callee.lookup (ofString "msg")=some (.val (.word message)) ∧ callee.lookup (ofString "kind")=some (.val (.word kind)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values message kind).length ∧
      ((formals.zip (values message kind)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
    decide
  have raw : lookupCodeHOLExact code (ofString "frame_open") (values message kind)=some (body,rawLocals message kind,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup code (ofString "frame_open") (values message kind) body (rawLocals message kind) .one raw
  refine ⟨callee,called,?_,?_⟩
  · rw [locals]; simp [rawLocals,show ofString "msg"≠ofString "kind" from by decide]
  · rw [locals]; simp [rawLocals]

def childCall : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def recordCall : ProgHOL 64:=match childCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterRecord : ProgHOL 64:=match recordCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterClear : ProgHOL 64:=match afterRecord with | .seq _ rest=>rest | _=>.skip
def clear : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "rec",.const 104#64]

theorem shapes : body=.dec (ofString "parent") .one (.var .global (ofString "ev")) childCall ∧
    childCall=.decCall (ofString "child") .one (ofString "frame_new") [localVar "msg"] recordCall ∧
    recordCall=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 104#64] afterRecord ∧
    afterRecord=.seq clear afterClear := by
  simp only [body,childCall,recordCall,afterRecord,afterClear,clear,Guest.Software.guestFn_frame_open,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  trivial

theorem after_clear_price (code) : ClockCost.Bound code afterClear 0 := by
  apply ClockCost.of_quiet
  simp only [afterClear,afterRecord,recordCall,childCall,body,Guest.Software.guestFn_frame_open,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply QuietClock.sequence
    | exact QuietClock.store code _ _
    | exact QuietClock.assign_kind code _ _ _
    | exact QuietClock.returned code _

/-- Once frame_new returns, the remaining allocation, fixed-length clear,
stores, activation and return have a uniform cost, even when they fail. -/
theorem record_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code recordCall 136 := by
  have zeroCost : ClockCost.Bound code clear 134 := by
    intro source codeEq
    have current : OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
    exact ZeroAny.dynamic_call_cost source (localVar "rec") 104 (by decide) (Zero.original_code source.code current)
  have tail:=ClockCost.sequence code clear afterClear 134 0 zeroCost (after_clear_price code)
  rw [shapes.2.2.1,shapes.2.2.2]
  exact Arenas.scoped_price code installed .down (ofString "rec") .one [.const 104#64] _ 134 (by simpa only [Nat.add_zero] using tail)

abbrev bodyPrice : Nat:=65967

/-- The original frame_open body, priced from the real message entry. Parent
reads may fail; no parent value, future child success or allocation is assumed. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (messageCell : source.locals.lookup (ofString "msg")=some (.val (.word message))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤bodyPrice := by
  rw [shapes.1]
  apply ClockCost.declared_reached_current
  intro value read checked
  let parent:=setVarHOLFinite (ofString "parent") value source
  have current : MessageExecution.Memory parent bs te message target input length accounts storage:=state.of_erase rfl
  have msg : parent.locals.lookup (ofString "msg")=some (.val (.word message)) := by
    simpa [parent,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using messageCell
  have args : evalListHOLFinite parent (h:=fun address=>Classical.propDecidable (parent.memaddrs address)) [localVar "msg"]=some [.val (.word message)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,msg]
  obtain ⟨callee,called,cell⟩:=word_environment parent.code.lookup (ofString "frame_new") (ofString "msg") FrameConstruction.body .one message
    (FrameConstruction.original_code parent.code current.environment.arena.code)
  have price:=FrameConstruction.body_cost (current.of_erase (show LocalEffects.erase (callEntryStateHOLFinite parent callee)=LocalEffects.erase parent from rfl)) cell
  rw [shapes.2.1]
  exact ClockCost.scoped_current parent (ofString "child") .one (ofString "frame_new") [localVar "msg"] [.val (.word message)]
    FrameConstruction.body recordCall callee .one FrameConstruction.bodyPrice 136 args called price (record_price parent.code current.environment.arena.code)

/-- The actual process_message frame_open(msg,0) ABI retains the full physical
message model when the caller's locals are replaced by the two formals. -/
theorem call_environment {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Entry source bs te message target input length accounts storage) (kind : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "frame_open") (values message kind)=some (body,callee,.one) ∧
      MessageExecution.Entry (callEntryStateHOLFinite source callee) bs te message target input length accounts storage ∧
      callee.lookup (ofString "kind")=some (.val (.word kind)) := by
  obtain ⟨callee,called,msg,kindCell⟩:=environment source.code.lookup message kind (original_code source.code state.memory.environment.arena.code)
  exact ⟨callee,called,⟨state.memory.of_erase rfl,msg⟩,kindCell⟩

end InitECandidate.Solver.Input.CurrentVerify.FrameOpening

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.after_clear_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.call_environment

namespace InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable def arrayAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (cursor amount : BitVec 64) :=
  QueryBranch.bind (Arenas.post {source with clock:=source.clock-1} .down cursor amount) name (Arenas.rounded .down cursor amount)
noncomputable def arrayStored (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (table cursor amount : BitVec 64) (offset : Nat) :=
  {arrayAllocated source name cursor amount with memory:=WordWrites.write source.memory [(table+BitVec.ofNat 64 offset,Arenas.rounded .down cursor amount)]}

/-- Execute an actual downward allocation followed by its real header-pointer
store. The pointer, room, returned word and memory effect are derived from the
allocator implementation. The enclosing continuation remains unchanged. -/
theorem array_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (table cursor lower amount : BitVec 64) (offset : Nat)
    (notTable : ofString name≠ofString "t")
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word amount)])
    (code : source.code.lookup (ofString "scratch_alloc")=some (Arenas.formals,Arenas.body .down,.one))
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)))
    (lowerCell : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (aligned : lower.toNat%8=0) (room : lower.toNat+amount.toNat≤cursor.toNat)
    (mapped : source.memaddrs (table+BitVec.ofNat 64 offset)) (enough : 1≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "scratch_alloc") arguments
      (.seq (.store (FieldStores.address "t" offset) (localVar name)) continuation))=
      (let output:=evaluateHOLFiniteState (arrayStored source name table cursor amount offset) continuation
       (output.1,restore source name output.2)) := by
  let allocated:=arrayAllocated source name cursor amount
  let field : FieldStores.Field:=⟨offset,.saved name (Arenas.rounded .down cursor amount)⟩
  have retained : allocated.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ name "t" _ notTable).trans tableCell
  have saved : allocated.locals.lookup (ofString name)=some (.val (.word (Arenas.rounded .down cursor amount))):=bind_lookup_same _ _ _
  have reads : ∀ entry∈[field],entry.value.Ready allocated "unused" 0#64 := by
    intro entry member
    have same : entry=field:=by simpa only [List.mem_singleton] using member
    subst entry
    exact saved
  have maps : ∀ entry∈[field],allocated.memaddrs (table+BitVec.ofNat 64 entry.offset) := by
    intro entry member
    have same : entry=field:=by simpa only [List.mem_singleton] using member
    subst entry
    exact mapped
  have avoid : ∀ reader∈[field],∀ writer∈[field],reader.value.Avoid 0#64 (table+BitVec.ofNat 64 writer.offset) := by
    intro reader member writer inside
    have same : reader=field:=by simpa only [List.mem_singleton] using member
    subst reader
    trivial
  have stored:=FieldStores.execute allocated "t" "unused" table 0#64 [field] retained reads maps avoid continuation
  change evaluateHOLFiniteState allocated (.seq (.store (FieldStores.address "t" offset) (localVar name)) continuation)=
    evaluateHOLFiniteState (arrayStored source name table cursor amount offset) continuation at stored
  have called:=Arenas.call_execute source .down name arguments
    (.seq (.store (FieldStores.address "t" offset) (localVar name)) continuation) cursor lower amount args code cursorCell lowerCell aligned room enough
  change evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "scratch_alloc") arguments _)=
    (let output:=evaluateHOLFiniteState allocated (.seq (.store (FieldStores.address "t" offset) (localVar name)) continuation)
     (output.1,restore source name output.2)) at called
  rw [stored] at called
  exact called

theorem array_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (table cursor amount : BitVec 64) (offset : Nat) :
    (arrayStored source name table cursor amount offset).clock=source.clock-1 := rfl

theorem array_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (table cursor amount query : BitVec 64) (offset : Nat)
    (away : query≠table+BitVec.ofNat 64 offset) :
    (arrayStored source name table cursor amount offset).memory query=source.memory query := by
  apply WordWrites.write_away
  simpa only [List.map_cons,List.map_nil,List.mem_singleton] using away

def headerFields : List FieldStores.Field:=
  [⟨0,.saved "key_len" 20#64⟩,⟨8,.saved "stride" 24#64⟩,⟨16,.saved "cap" 4#64⟩,⟨24,.literal 0#64⟩]
def finalFields : List FieldStores.Field:=
  [⟨56,.literal 0#64⟩,⟨64,.literal 1#64⟩,⟨72,.literal 0#64⟩,⟨80,.saved "ncap" 4#64⟩]
def strideExpression : ExpHOL 64:=.op .and [.op .add [localVar "key_len",.const 7#64],.op .sub [.const 0#64,.const 8#64]]
def capacityGuard : ProgHOL 64:=.ite (.cmp .lower (localVar "ncap") (.const 2#64)) (.assign .local (ofString "ncap") (.const 2#64)) .skip
def keysAmount : ExpHOL 64:=.panop .mul [.op .add [localVar "ncap",.const 1#64],localVar "stride"]
def nodesAmount : ExpHOL 64:=.panop .mul [.op .add [localVar "ncap",.const 1#64],.const 32#64]
def orderAmount : ExpHOL 64:=.panop .mul [.op .add [localVar "ncap",.const 1#64],.const 8#64]

def afterHeader : ProgHOL 64:=match FrameConstruction.tableBody with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterStride : ProgHOL 64:=match afterHeader with | .dec _ _ _ rest=>rest | _=>.skip
def afterCapacity : ProgHOL 64:=match afterStride with | .dec _ _ _ rest=>rest | _=>.skip
def afterGuard : ProgHOL 64:=match afterCapacity with | .seq _ rest=>rest | _=>.skip
def keysCall : ProgHOL 64:=UncheckedSystem.dropCommands 4 afterGuard
def nodesCall : ProgHOL 64:=match keysCall with | .decCall _ _ _ _ (.seq _ rest)=>rest | _=>.skip
def orderCall : ProgHOL 64:=match nodesCall with | .decCall _ _ _ _ (.seq _ rest)=>rest | _=>.skip
def finish : ProgHOL 64:=match orderCall with | .decCall _ _ _ _ (.seq _ rest)=>rest | _=>.skip

theorem shapes : FrameConstruction.tableBody=.decCall (ofString "t") .one (ofString "scratch_alloc") [.const 88#64] afterHeader ∧
    afterHeader=.dec (ofString "stride") .one strideExpression
      (.dec (ofString "ncap") .one (localVar "cap") (.seq capacityGuard (FieldStores.program "t" "unused" headerFields keysCall))) ∧
    keysCall=.decCall (ofString "keys") .one (ofString "scratch_alloc") [keysAmount]
      (.seq (.store (FieldStores.address "t" 32) (localVar "keys")) nodesCall) ∧
    nodesCall=.decCall (ofString "nodes") .one (ofString "scratch_alloc") [nodesAmount]
      (.seq (.store (FieldStores.address "t" 40) (localVar "nodes")) orderCall) ∧
    orderCall=.decCall (ofString "order") .one (ofString "scratch_alloc") [orderAmount]
      (.seq (.store (FieldStores.address "t" 48) (localVar "order")) finish) ∧
    finish=FieldStores.program "t" "unused" finalFields (.return (localVar "t")) := by
  simp only [afterHeader,afterStride,afterCapacity,afterGuard,keysCall,nodesCall,orderCall,finish,
    FrameConstruction.tableBody,Guest.Software.guestFn_htab_new_scratch,UncheckedSystem.dropCommands,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    strideExpression,capacityGuard,keysAmount,nodesAmount,orderAmount,headerFields,finalFields,
    FieldStores.program,FieldStores.address,FieldStores.Value.expression,localVar,addConst]
  trivial

noncomputable def declarations (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  QueryBranch.bind (QueryBranch.bind source "stride" 24#64) "ncap" 4#64
noncomputable def headerStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) :=
  {declarations source with memory:=WordWrites.write source.memory (FieldStores.writes table headerFields)}

/-- The actual scalar20/4 prefix computes stride24, keeps ncap4 and writes
all four initial fields. No persistent-allocator proof or old hash layout is
used for this current scratch constructor. -/
theorem header_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word 20#64)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word 4#64)))
    (mapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs (table+BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState source afterHeader=
      (let output:=evaluateHOLFiniteState (headerStored source table) keysCall
       (output.1,restore source "stride" (restore (QueryBranch.bind source "stride" 24#64) "ncap" output.2))) := by
  let ready:=declarations source
  let fields:=FieldStores.program "t" "unused" headerFields keysCall
  have kept (name : String) (notCap : ofString "ncap"≠ofString name) (notStride : ofString "stride"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other _ "ncap" name _ notCap).trans (bind_lookup_other source "stride" name _ notStride)
  have tableReady : ready.locals.lookup (ofString "t")=some (.val (.word table)):=
    (kept "t" (by decide) (by decide)).trans tableCell
  have reads : ∀ field∈headerFields,field.value.Ready ready "unused" 0#64 := by
    intro field member
    simp only [headerFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact (kept "key_len" (by decide) (by decide)).trans keyCell
    · exact (bind_lookup_other _ "ncap" "stride" _ (by decide)).trans (bind_lookup_same source "stride" 24#64)
    · exact (kept "cap" (by decide) (by decide)).trans capCell
    · trivial
  have maps : ∀ field∈headerFields,ready.memaddrs (table+BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    all_goals
      simp only [headerFields,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
  have avoid : ∀ reader∈headerFields,∀ writer∈headerFields,reader.value.Avoid 0#64 (table+BitVec.ofNat 64 writer.offset) := by
    intro reader member writer inside
    simp only [headerFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> trivial
  have stores:=FieldStores.execute ready "t" "unused" table 0#64 headerFields tableReady reads maps avoid keysCall
  change evaluateHOLFiniteState ready fields=evaluateHOLFiniteState (headerStored source table) keysCall at stores
  have ncapCell : ready.locals.lookup (ofString "ncap")=some (.val (.word 4#64)):=bind_lookup_same _ _ _
  have guard : evaluateHOLFiniteState ready capacityGuard=(none,ready) := by
    simp [capacityGuard,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,toExact,localVar,ncapCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  have guarded:=StateSteps.next_sequence ready ready capacityGuard fields guard (Nat.le_refl _)
  rw [stores] at guarded
  let output:=evaluateHOLFiniteState (headerStored source table) keysCall
  have currentCap : eval (QueryBranch.bind source "stride" 24#64) (localVar "cap")=some (.val (.word 4#64)) := by
    have cell : (QueryBranch.bind source "stride" 24#64).locals.lookup (ofString "cap")=some (.val (.word 4#64)):=
      (bind_lookup_other source "stride" "cap" 24#64 (by decide)).trans capCell
    simp [eval,evalHOLExact,toExact,localVar,cell]
  have declaredCap:=ScalarScope.declare_execute (QueryBranch.bind source "stride" 24#64) output.2 "ncap" (localVar "cap") 4#64
    (.seq capacityGuard fields) output.1 currentCap guarded
  have strideRead : eval source strideExpression=some (.val (.word 24#64)) := by
    simp [eval,strideExpression,evalHOLExact,evalListHOLExact,toExact,localVar,keyCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    decide
  have declaredStride:=ScalarScope.declare_execute source _ "stride" strideExpression 24#64
    (.dec (ofString "ncap") .one (localVar "cap") (.seq capacityGuard fields)) output.1 strideRead declaredCap
  rw [shapes.2.1]
  exact declaredStride

def header (scratch : BitVec 64) : BitVec 64:=Arenas.rounded .down scratch 88#64
def keys (scratch : BitVec 64) : BitVec 64:=Arenas.rounded .down (header scratch) 120#64
def nodes (scratch : BitVec 64) : BitVec 64:=Arenas.rounded .down (keys scratch) 160#64
def nextScratch (scratch : BitVec 64) : BitVec 64:=Arenas.rounded .down (nodes scratch) 40#64

structure Geometry (scratch : BitVec 64) : Prop where
  headerNumber : (header scratch).toNat=scratch.toNat-88
  keysNumber : (keys scratch).toNat=scratch.toNat-208
  nodesNumber : (nodes scratch).toNat=scratch.toNat-368
  nextNumber : (nextScratch scratch).toNat=scratch.toNat-408
  headerAligned : (header scratch).toNat%8=0
  keysAligned : (keys scratch).toNat%8=0
  nodesAligned : (nodes scratch).toNat%8=0
  nextAligned : (nextScratch scratch).toNat%8=0

/-- Actual current20/4 scratch Patricia geometry:88-byte header,120-byte keys,
160-byte nodes and40-byte order array. All four addresses come from the real
allocator's rounded result; the former272-byte hash-table reserve is absent. -/
theorem geometry (scratch : BitVec 64) (aligned : scratch.toNat%8=0) (room : 408≤scratch.toNat) : Geometry scratch := by
  have first:=Arenas.rounded_down_nat scratch 88#64 (by change 88≤scratch.toNat; omega)
  have hn : (header scratch).toNat=scratch.toNat-88 := by
    change (header scratch).toNat=(scratch.toNat-88)/8*8 at first
    omega
  have ha : (header scratch).toNat%8=0 := by rw [hn]; omega
  have second:=Arenas.rounded_down_nat (header scratch) 120#64 (by change 120≤(header scratch).toNat; omega)
  have kn : (keys scratch).toNat=scratch.toNat-208 := by
    change (keys scratch).toNat=((header scratch).toNat-120)/8*8 at second
    omega
  have ka : (keys scratch).toNat%8=0 := by rw [kn]; omega
  have third:=Arenas.rounded_down_nat (keys scratch) 160#64 (by change 160≤(keys scratch).toNat; omega)
  have nn : (nodes scratch).toNat=scratch.toNat-368 := by
    change (nodes scratch).toNat=((keys scratch).toNat-160)/8*8 at third
    omega
  have na : (nodes scratch).toNat%8=0 := by rw [nn]; omega
  have fourth:=Arenas.rounded_down_nat (nodes scratch) 40#64 (by change 40≤(nodes scratch).toNat; omega)
  have en : (nextScratch scratch).toNat=scratch.toNat-408 := by
    change (nextScratch scratch).toNat=((nodes scratch).toNat-40)/8*8 at fourth
    omega
  exact ⟨hn,kn,nn,en,ha,ka,na,by rw [en]; omega⟩

noncomputable def finalStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) :=
  {source with memory:=WordWrites.write source.memory (FieldStores.writes table finalFields)}

/-- The genuine final four metadata stores and return establish the empty
Patricia root/node state. This is execution evidence, not an assumed image. -/
theorem finish_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (capacityCell : source.locals.lookup (ofString "ncap")=some (.val (.word 4#64)))
    (mapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs (table+BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState source finish=(some (.returned (.val (.word table))),emptyLocalsHOLFinite (finalStored source table)) := by
  have reads : ∀ field∈finalFields,field.value.Ready source "unused" 0#64 := by
    intro field member
    simp only [finalFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · trivial
    · trivial
    · trivial
    · exact capacityCell
  have maps : ∀ field∈finalFields,source.memaddrs (table+BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    all_goals
      simp only [finalFields,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
  have avoid : ∀ reader∈finalFields,∀ writer∈finalFields,reader.value.Avoid 0#64 (table+BitVec.ofNat 64 writer.offset) := by
    intro reader member writer inside
    simp only [finalFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> trivial
  have stores:=FieldStores.execute source "t" "unused" table 0#64 finalFields tableCell reads maps avoid (.return (localVar "t"))
  rw [shapes.2.2.2.2.2,stores]
  simp [evaluateHOLFiniteState_return,localVar,evalHOLExact,toExact,tableCell,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rfl

theorem array_local_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (table cursor amount : BitVec 64) (offset : Nat) (key : MlS) (other : ofString name≠key) :
    (arrayStored source name table cursor amount offset).locals.lookup key=source.locals.lookup key := by
  change (source.locals.update (ofString name,.val (.word (Arenas.rounded .down cursor amount)))).lookup key=_
  simp [HolFiniteMapExact.update,FUPDATE,other]

theorem array_scratch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (table cursor amount : BitVec 64) (offset : Nat) :
    (arrayStored source name table cursor amount offset).globals.lookup (ofString "scratch_ptr")=
      some (.val (.word (Arenas.rounded .down cursor amount))) := by
  change (source.globals.update (ofString "scratch_ptr",.val (.word (Arenas.rounded .down cursor amount)))).lookup _=_
  simp [HolFiniteMapExact.update,FUPDATE]

theorem array_lower (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (table cursor amount : BitVec 64) (offset : Nat) :
    (arrayStored source name table cursor amount offset).globals.lookup (ofString "frame_mem_ptr")=
      source.globals.lookup (ofString "frame_mem_ptr") := by
  change (source.globals.update (ofString "scratch_ptr",.val (.word (Arenas.rounded .down cursor amount)))).lookup _=_
  simp [HolFiniteMapExact.update,FUPDATE,ofString]

noncomputable def keysStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64):=
  arrayStored source "keys" (header scratch) (header scratch) 120#64 32
noncomputable def nodesStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64):=
  arrayStored (keysStored source scratch) "nodes" (header scratch) (keys scratch) 160#64 40
noncomputable def orderStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64):=
  arrayStored (nodesStored source scratch) "order" (header scratch) (nodes scratch) 40#64 48
noncomputable def arraysFinal (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64):=
  finalStored (orderStored source scratch) (header scratch)

/-- All three current backing-array calls, every pointer/header store and
return. The real downward cursor advances by320bytes after the header; all
normal helper executions are derived from the incoming physical room. -/
theorem arrays_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch lower : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word (header scratch))))
    (capacityCell : source.locals.lookup (ofString "ncap")=some (.val (.word 4#64)))
    (strideCell : source.locals.lookup (ofString "stride")=some (.val (.word 24#64)))
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word (header scratch))))
    (lowerCell : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (scratchAligned : scratch.toNat%8=0) (lowerAligned : lower.toNat%8=0)
    (room : lower.toNat+408≤scratch.toNat)
    (mapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs (header scratch+BitVec.ofNat 64 offset))
    (enough : 3≤source.clock) :
    ∃ post,evaluateHOLFiniteState source keysCall=(some (.returned (.val (.word (header scratch)))),post) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite (arraysFinal source scratch) := by
  have layout:=geometry scratch scratchAligned (by omega)
  let first:=keysStored source scratch
  let second:=nodesStored source scratch
  let third:=orderStored source scratch
  have firstTable : first.locals.lookup (ofString "t")=some (.val (.word (header scratch))):=
    (array_local_other source "keys" _ _ _ 32 _ (by decide)).trans tableCell
  have secondTable : second.locals.lookup (ofString "t")=some (.val (.word (header scratch))):=
    (array_local_other first "nodes" _ _ _ 40 _ (by decide)).trans firstTable
  have thirdTable : third.locals.lookup (ofString "t")=some (.val (.word (header scratch))):=
    (array_local_other second "order" _ _ _ 48 _ (by decide)).trans secondTable
  have firstCap : first.locals.lookup (ofString "ncap")=some (.val (.word 4#64)):=
    (array_local_other source "keys" _ _ _ 32 _ (by decide)).trans capacityCell
  have secondCap : second.locals.lookup (ofString "ncap")=some (.val (.word 4#64)):=
    (array_local_other first "nodes" _ _ _ 40 _ (by decide)).trans firstCap
  have thirdCap : third.locals.lookup (ofString "ncap")=some (.val (.word 4#64)):=
    (array_local_other second "order" _ _ _ 48 _ (by decide)).trans secondCap
  have keyArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [keysAmount]=some [.val (.word 120#64)] := by
    simp [keysAmount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,capacityCell,strideCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have nodeArgs : evalListHOLFinite first (h:=fun address=>Classical.propDecidable (first.memaddrs address)) [nodesAmount]=some [.val (.word 160#64)] := by
    simp [nodesAmount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,firstCap,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have orderArgs : evalListHOLFinite second (h:=fun address=>Classical.propDecidable (second.memaddrs address)) [orderAmount]=some [.val (.word 40#64)] := by
    simp [orderAmount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,secondCap,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have tail:=finish_execute third (header scratch) thirdTable thirdCap mapped
  have orderRun:=array_execute second "order" [orderAmount] finish (header scratch) (nodes scratch) lower 40#64 48
    (by decide) orderArgs (Arenas.original_code source.code installed .down) (array_scratch first "nodes" _ _ _ 40)
    ((array_lower first "nodes" _ _ _ 40).trans ((array_lower source "keys" _ _ _ 32).trans lowerCell)) secondTable lowerAligned
    (by change lower.toNat+40≤(nodes scratch).toNat; have number:=layout.nodesNumber; omega) (mapped 48 (by decide) (by decide))
    (by change 1≤source.clock-1-1; omega)
  change evaluateHOLFiniteState second (.decCall (ofString "order") .one (ofString "scratch_alloc") [orderAmount] _)=
    (let output:=evaluateHOLFiniteState third finish; (output.1,restore second "order" output.2)) at orderRun
  rw [tail] at orderRun
  rw [←shapes.2.2.2.2.1] at orderRun
  have nodeRun:=array_execute first "nodes" [nodesAmount] orderCall (header scratch) (keys scratch) lower 160#64 40
    (by decide) nodeArgs (Arenas.original_code source.code installed .down) (array_scratch source "keys" _ _ _ 32)
    ((array_lower source "keys" _ _ _ 32).trans lowerCell) firstTable lowerAligned
    (by change lower.toNat+160≤(keys scratch).toNat; have number:=layout.keysNumber; omega) (mapped 40 (by decide) (by decide))
    (by change 1≤source.clock-1; omega)
  change evaluateHOLFiniteState first (.decCall (ofString "nodes") .one (ofString "scratch_alloc") [nodesAmount] _)=
    (let output:=evaluateHOLFiniteState second _; (output.1,restore first "nodes" output.2)) at nodeRun
  rw [orderRun] at nodeRun
  rw [←shapes.2.2.2.1] at nodeRun
  have keyRun:=array_execute source "keys" [keysAmount] nodesCall (header scratch) (header scratch) lower 120#64 32
    (by decide) keyArgs (Arenas.original_code source.code installed .down) cursorCell lowerCell tableCell lowerAligned
    (by change lower.toNat+120≤(header scratch).toNat; have number:=layout.headerNumber; omega) (mapped 32 (by decide) (by decide)) (by omega)
  change evaluateHOLFiniteState source (.decCall (ofString "keys") .one (ofString "scratch_alloc") [keysAmount] _)=
    (let output:=evaluateHOLFiniteState first _; (output.1,restore source "keys" output.2)) at keyRun
  rw [nodeRun] at keyRun
  rw [←shapes.2.2.1] at keyRun
  refine ⟨restore source "keys" (restore first "nodes" (restore second "order" (emptyLocalsHOLFinite (arraysFinal source scratch)))),?_,rfl⟩
  exact keyRun

noncomputable def finalState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  arraysFinal (headerStored (arrayAllocated source "t" scratch 88#64) (header scratch)) scratch

def writes (scratch : BitVec 64) : List (BitVec 64×BitVec 64):=
  [(header scratch+0#64,20#64),(header scratch+8#64,24#64),(header scratch+16#64,4#64),(header scratch+24#64,0#64),
   (header scratch+32#64,keys scratch),(header scratch+40#64,nodes scratch),(header scratch+48#64,nextScratch scratch),
   (header scratch+56#64,0#64),(header scratch+64#64,1#64),(header scratch+72#64,0#64),(header scratch+80#64,4#64)]

theorem final_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :
    (finalState source scratch).memory=WordWrites.write source.memory (writes scratch) := by rfl

theorem writes_distinct (scratch : BitVec 64) : ((writes scratch).map Prod.fst).Nodup := by
  change (([0#64,8#64,16#64,24#64,32#64,40#64,48#64,56#64,64#64,72#64,80#64] : List (BitVec 64)).map (fun offset=>header scratch+offset)).Nodup
  apply List.Nodup.map (fun left right same=>(BitVec.add_right_inj (header scratch)).mp same)
  decide

theorem final_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64)
    (field : BitVec 64×BitVec 64) (member : field∈writes scratch) :
    (finalState source scratch).memory field.1=.word field.2 := by
  rw [final_memory]
  exact WordWrites.write_unique source.memory (writes scratch) field (writes_distinct scratch) member

theorem final_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :
    (finalState source scratch).clock=source.clock-4 := by
  change source.clock-1-1-1-1=source.clock-4
  omega

theorem final_scratch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :
    (finalState source scratch).globals.lookup (ofString "scratch_ptr")=some (.val (.word (nextScratch scratch))) :=
  array_scratch (nodesStored (headerStored (arrayAllocated source "t" scratch 88#64) (header scratch)) scratch)
    "order" (header scratch) (nodes scratch) 40#64 48

/-- Exact current20/4 scratch-table execution: four real allocations,
all eleven actual metadata writes and the returned header. Every helper
execution is proved from entry room/code/clock facts; none is assumed. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch lower : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word 20#64)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word 4#64)))
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (lowerCell : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (scratchAligned : scratch.toNat%8=0) (lowerAligned : lower.toNat%8=0)
    (room : lower.toNat+408≤scratch.toNat)
    (mapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs (header scratch+BitVec.ofNat 64 offset))
    (enough : 4≤source.clock) :
    ∃ post,evaluateHOLFiniteState source FrameConstruction.tableBody=(some (.returned (.val (.word (header scratch)))),post) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite (finalState source scratch) := by
  let allocated:=arrayAllocated source "t" scratch 88#64
  let ready:=headerStored allocated (header scratch)
  have tableCell : allocated.locals.lookup (ofString "t")=some (.val (.word (header scratch))):=bind_lookup_same _ _ _
  have keyAllocated : allocated.locals.lookup (ofString "key_len")=some (.val (.word 20#64)):=
    (bind_lookup_other _ "t" "key_len" _ (by decide)).trans keyCell
  have capAllocated : allocated.locals.lookup (ofString "cap")=some (.val (.word 4#64)):=
    (bind_lookup_other _ "t" "cap" _ (by decide)).trans capCell
  have tableReady : ready.locals.lookup (ofString "t")=some (.val (.word (header scratch))):=
    (bind_lookup_other _ "ncap" "t" _ (by decide)).trans
      ((bind_lookup_other _ "stride" "t" _ (by decide)).trans tableCell)
  have capReady : ready.locals.lookup (ofString "ncap")=some (.val (.word 4#64)):=bind_lookup_same _ _ _
  have strideReady : ready.locals.lookup (ofString "stride")=some (.val (.word 24#64)):=
    (bind_lookup_other _ "ncap" "stride" _ (by decide)).trans (bind_lookup_same _ _ _)
  have cursorReady : ready.globals.lookup (ofString "scratch_ptr")=some (.val (.word (header scratch))):=
    array_scratch source "t" (header scratch) scratch 88#64 0
  have lowerReady : ready.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)):=
    (array_lower source "t" (header scratch) scratch 88#64 0).trans lowerCell
  obtain ⟨arraysPost,arraysRun,arraysFrame⟩:=arrays_execute ready scratch lower installed tableReady capReady strideReady cursorReady lowerReady
    scratchAligned lowerAligned room mapped (by change 3≤source.clock-1; omega)
  have headerRun:=header_execute allocated (header scratch) tableCell keyAllocated capAllocated mapped
  change evaluateHOLFiniteState allocated afterHeader=
    (let output:=evaluateHOLFiniteState ready keysCall
     (output.1,restore allocated "stride" (restore (QueryBranch.bind allocated "stride" 24#64) "ncap" output.2))) at headerRun
  rw [arraysRun] at headerRun
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 88#64]=some [.val (.word 88#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have allocationRun:=Arenas.call_execute source .down "t" [.const 88#64] afterHeader scratch lower 88#64 args
    (Arenas.original_code source.code installed .down) cursorCell lowerCell lowerAligned
    (by change lower.toNat+88≤scratch.toNat; omega) (by omega)
  change evaluateHOLFiniteState source (.decCall (ofString "t") .one (ofString "scratch_alloc") [.const 88#64] afterHeader)=
    (let output:=evaluateHOLFiniteState allocated afterHeader; (output.1,restore source "t" output.2)) at allocationRun
  rw [headerRun,←shapes.1] at allocationRun
  refine ⟨restore source "t" (restore allocated "stride" (restore (QueryBranch.bind allocated "stride" 24#64) "ncap" arraysPost)),allocationRun,?_⟩
  exact arraysFrame

theorem final_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :
    (finalState source scratch).globals=source.globals.update (ofString "scratch_ptr",.val (.word (nextScratch scratch))) := by
  have overwrite (globals : HolFiniteMapExact MlS (ValueHOL 64)) (first last : BitVec 64) :
      (globals.update (ofString "scratch_ptr",.val (.word first))).update (ofString "scratch_ptr",.val (.word last))=
        globals.update (ofString "scratch_ptr",.val (.word last)) := by
    apply HolFiniteMapExact.ext
    funext query
    by_cases same : ofString "scratch_ptr"=query <;> simp [HolFiniteMapExact.update,FUPDATE,same]
  change (((source.globals.update (ofString "scratch_ptr",.val (.word (header scratch)))).update
    (ofString "scratch_ptr",.val (.word (keys scratch)))).update (ofString "scratch_ptr",.val (.word (nodes scratch)))).update
      (ofString "scratch_ptr",.val (.word (nextScratch scratch)))=_
  rw [overwrite,overwrite,overwrite]

/-- Only the actual88-byte header is written; the allocated backing arrays
need no assumed initial contents. Earlier and older scratch objects survive. -/
theorem final_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch query : BitVec 64)
    (away : ∀ offset<88,query≠header scratch+BitVec.ofNat 64 offset) :
    (finalState source scratch).memory query=source.memory query := by
  rw [final_memory]
  apply WordWrites.write_away
  simp only [writes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨away 0 (by decide),away 8 (by decide),away 16 (by decide),away 24 (by decide),away 32 (by decide),
    away 40 (by decide),away 48 (by decide),away 56 (by decide),away 64 (by decide),away 72 (by decide),away 80 (by decide)⟩

noncomputable def callPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (scratch : BitVec 64) :=
  QueryBranch.bind {finalState {source with clock:=source.clock-1} scratch with locals:=source.locals} name (header scratch)

/-- Actual scoped20/4 constructor call with the exact current memory/cursor
result and original caller restoration. This bridges the new normal execution
to its unchanged caller, without requiring a callee result as a premise. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (scratch lower : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word 20#64),.val (.word 4#64)])
    (installed : OriginalCode.Installed source.code)
    (cursorCell : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (lowerCell : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (scratchAligned : scratch.toNat%8=0) (lowerAligned : lower.toNat%8=0)
    (room : lower.toNat+408≤scratch.toNat)
    (mapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs (header scratch+BitVec.ofNat 64 offset))
    (enough : 5≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new_scratch") arguments continuation)=
      (let output:=evaluateHOLFiniteState (callPost source name scratch) continuation; (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,keyCell,capCell⟩:=word_pair_environment source.code.lookup (ofString "htab_new_scratch") (ofString "key_len") (ofString "cap")
    FrameConstruction.tableBody .one 20#64 4#64 (by decide) (FrameConstruction.table_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨post,run,frame⟩:=execute entry scratch lower installed keyCell capCell cursorCell lowerCell scratchAligned lowerAligned room mapped
    (by change 4≤source.clock-1; omega)
  have actual:=CallNormal.return_execute source post name .one (ofString "htab_new_scratch") arguments
    [.val (.word 20#64),.val (.word 4#64)] FrameConstruction.tableBody continuation callee .one (.val (.word (header scratch)))
    args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {post with locals:=source.locals}={finalState {source with clock:=source.clock-1} scratch with locals:=source.locals} at callerFrame
  have next:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) (.val (.word (header scratch))) state) callerFrame
  change CallNormal.continuationEntry source post name (.val (.word (header scratch)))=callPost source name scratch at next
  rw [next] at actual
  exact actual

theorem call_post_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (scratch : BitVec 64)
    (field : BitVec 64×BitVec 64) (member : field∈writes scratch) :
    (callPost source name scratch).memory field.1=.word field.2 := final_field _ scratch field member

theorem call_post_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (scratch : BitVec 64) :
    (callPost source name scratch).clock=source.clock-5 := by
  change (finalState {source with clock:=source.clock-1} scratch).clock=source.clock-5
  rw [final_clock]
  change source.clock-1-4=source.clock-5
  omega

theorem call_post_canonical (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (scratch : BitVec 64) :
    callPost source name scratch=QueryBranch.bind {source with
      globals:=source.globals.update (ofString "scratch_ptr",.val (.word (nextScratch scratch)))
      memory:=WordWrites.write source.memory (writes scratch)
      clock:=source.clock-5} name (header scratch) := by
  unfold callPost
  change QueryBranch.bind {source with
    globals:=(finalState {source with clock:=source.clock-1} scratch).globals
    memory:=WordWrites.write source.memory (writes scratch)
    clock:=source.clock-1-1-1-1-1} name (header scratch)=_
  rw [final_globals]
  have clocks : source.clock-1-1-1-1-1=source.clock-5:=by omega
  rw [clocks]

end InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.array_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.array_clock
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.array_memory_away

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.header_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.geometry
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.finish_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.arrays_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.final_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.writes_distinct
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.final_field
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.final_clock
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.final_scratch
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.final_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.final_memory_away
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.call_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.call_post_field
#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.call_post_clock

#print axioms InitECandidate.Solver.Input.CurrentVerify.ScratchPatricia.call_post_canonical

namespace InitECandidate.Solver.Input.CurrentVerify.FrameNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open GasBudget GasBudget.FrameNew
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Only these eight frame cells are written after the log/status/message
stores. Keeping their own footprint avoids dropping facts about104/112. -/
def deleteStoreOffsets : List Nat:=[136,168,176,264,272,120,144,216]
def DeleteSafe (lower frame query : BitVec 64) : Prop:=
  (query.toNat<lower.toNat ∨ frame.toNat≤query.toNat) ∧
    ∀ offset∈deleteStoreOffsets,query≠frame+BitVec.ofNat 64 offset

theorem DeleteSafe.of_suffix {lower frame query : BitVec 64} (safe : SuffixSafe lower frame query) :
    DeleteSafe lower frame query := by
  refine ⟨safe.1,?_⟩
  intro offset member
  apply safe.2
  simp only [deleteStoreOffsets,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [suffixStoreOffsets]

theorem delete_safe_outside (lower frame cursor query : BitVec 64)
    (safe : DeleteSafe lower frame query) (above : cursor.toNat≤frame.toNat) :
    Arenas.Outside lower cursor query := by
  rcases safe.1 with below|high
  · exact Or.inl below
  · exact Or.inr (by omega)

theorem delete_link_safe (lower frame : BitVec 64) (offset : Nat)
    (member : offset∈([104,112] : List Nat)) (fits : frame.toNat+280<2^64) :
    DeleteSafe lower frame (frame+BitVec.ofNat 64 offset) := by
  refine ⟨Or.inr ?_,?_⟩
  · have inside : offset<280:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with rfl|rfl <;> decide
    have number : (frame+BitVec.ofNat 64 offset).toNat=frame.toNat+offset:=byteAddress_toNat frame offset (by omega)
    rw [number]
    omega
  · intro other otherIn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    simp only [deleteStoreOffsets,List.mem_cons,List.not_mem_nil,or_false] at otherIn
    rcases member with rfl|rfl <;>
      rcases otherIn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [BitVec.add_right_inj]

/-- Execute the real three stores following the delete-table call. -/
theorem delete_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message table : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (tableLocal : source.locals.lookup (ofString "del") = some (.val (.word table)))
    (separate : ∀ readOffset ∈ ([152, 160] : List Nat), ∀ writeOffset ∈ ([136, 168, 176] : List Nat),
      message + BitVec.ofNat 64 readOffset ≠ frame + BitVec.ofNat 64 writeOffset) :
    evaluateHOLFiniteState source deleteContinuation =
      evaluateHOLFiniteState {source with memory := (WitnessRadix.WordWrites.write source.memory
        (FieldStores.writes frame (deleteFields table words.addresses words.keys)))} countProgram := by
  have reads : ∀ field ∈ deleteFields table words.addresses words.keys,
      field.value.Ready source "msg" message := by
    intro field member
    simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact tableLocal
    · exact ready.copied 152 words.addresses (by simp [suffixCells])
    · exact ready.copied 160 words.keys (by simp [suffixCells])
  have mapped : ∀ field ∈ deleteFields table words.addresses words.keys,
      source.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ready.frameMapped _ (by dsimp <;> decide) (by dsimp <;> decide)
  have guarded : ∀ reader ∈ deleteFields table words.addresses words.keys,
      ∀ writer ∈ deleteFields table words.addresses words.keys,
        reader.value.Avoid message (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer writerIn
    have writeIn : writer.offset ∈ ([136, 168, 176] : List Nat) := by
      simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at writerIn
      rcases writerIn with rfl | rfl | rfl <;> simp
    simp only [deleteFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · trivial
    · exact separate 152 (by simp) writer.offset writeIn
    · exact separate 160 (by simp) writer.offset writeIn
  exact FieldStores.execute source "e" "msg" frame message (deleteFields table words.addresses words.keys)
    ready.frameLocal reads mapped guarded countProgram

/-- The real current Patricia delete-table call, its three frame stores,
both protected warm-count reads and final frame return. This complete actual
tail consumes7source ticks and keeps every protected prior frame word. -/
theorem delete_suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (installed : OriginalCode.Installed source.code)
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (scratchAligned : scratch.toNat%8=0) (lowerAligned : lower.toNat%8=0)
    (room : lower.toNat+408≤scratch.toNat) (frameAbove : scratch.toNat≤frame.toNat)
    (frameFits : frame.toNat+280<2^64)
    (inputsProtected : ∀ cell∈suffixCells message words,SuffixProtected lower frame cell.1)
    (mapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs (ScratchPatricia.header scratch+BitVec.ofNat 64 offset))
    (enough : 7≤source.clock) :
    ∃ target,evaluateHOLFiniteState source (.decCall (ofString "del") .one (ofString "htab_new_scratch")
        [.const 20#64,.const 4#64] deleteContinuation)=(some (.returned (.val (.word frame))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "scratch_ptr",.val (.word (ScratchPatricia.nextScratch scratch)))
        memory:=target.memory
        clock:=source.clock-7} ∧
      ∀ query,DeleteSafe lower frame query → target.memory query=source.memory query := by
  let tableMemory:=WordWrites.write source.memory (ScratchPatricia.writes scratch)
  have layout:=ScratchPatricia.geometry scratch scratchAligned (by omega)
  have tableFrame (query : BitVec 64) (outside : Arenas.Outside lower scratch query) : tableMemory query=source.memory query := by
    change (ScratchPatricia.finalState source scratch).memory query=source.memory query
    apply ScratchPatricia.final_memory_away
    intro offset inside same
    have headerNumber:=layout.headerNumber
    have noWrap : (ScratchPatricia.header scratch).toNat+offset<2^64 := by have upper:=scratch.isLt; omega
    have number : (ScratchPatricia.header scratch+BitVec.ofNat 64 offset).toNat=(ScratchPatricia.header scratch).toNat+offset:=byteAddress_toNat _ _ noWrap
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    rcases outside with below|above <;> omega
  have tableRun:=ScratchPatricia.call_execute source "del" [.const 20#64,.const 4#64] deleteContinuation scratch lower
    rfl installed scratchGlobal lowerGlobal scratchAligned lowerAligned room mapped (by omega)
  rw [ScratchPatricia.call_post_canonical] at tableRun
  have countCode : source.code.lookup (ofString "htab_count")=some (GasBudget.TableCount.formals,GasBudget.TableCount.body,.one):=
    FrameConstruction.count_code source.code installed
  let allocated := WitnessRadix.QueryBranch.bind {source with
    globals := source.globals.update (ofString "scratch_ptr", .val (.word (ScratchPatricia.nextScratch scratch)))
    memory := tableMemory
    clock := source.clock - 5} "del" (ScratchPatricia.header scratch)
  let stored := {allocated with memory := (WitnessRadix.WordWrites.write tableMemory
    (FieldStores.writes frame (deleteFields (ScratchPatricia.header scratch) words.addresses words.keys)))}
  have inputAway (cell : BitVec 64 × BitVec 64) (member : cell ∈ suffixCells message words)
      (offset : Nat) (inside : offset < 280) : cell.1 ≠ frame + BitVec.ofNat 64 offset :=
    suffix_protected_away lower frame cell.1 offset (inputsProtected cell member) (by omega) frameFits inside
  have allocatedReady : SuffixReady allocated frame message words empty := by
    have changed := (ready.memory tableMemory (by
      intro cell member
      exact tableFrame cell.1 (suffix_protected_outside lower frame scratch cell.1 (inputsProtected cell member) frameAbove))).scratch
      (ScratchPatricia.nextScratch scratch)
    exact (changed.clock (source.clock - 5)).bound "del" (ScratchPatricia.header scratch) (by decide) (by decide)
  have storedReady : SuffixReady stored frame message words empty := by
    apply allocatedReady.stored
    intro cell member
    simp only [FieldStores.writes, deleteFields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨inputAway cell member 136 (by decide), inputAway cell member 168 (by decide), inputAway cell member 176 (by decide)⟩
  have storesRun := delete_stores_execute allocated frame message (ScratchPatricia.header scratch) words empty
    allocatedReady (bind_lookup_same _ _ _) (by
      intro readOffset readIn writeOffset writeIn
      have protectedRead : SuffixProtected lower frame (message + BitVec.ofNat 64 readOffset) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at readIn
        rcases readIn with rfl | rfl
        · exact inputsProtected (message + 152#64, words.addresses) (by simp [suffixCells])
        · exact inputsProtected (message + 160#64, words.keys) (by simp [suffixCells])
      apply suffix_protected_away lower frame _ writeOffset protectedRead (by omega) frameFits
      simp only [List.mem_cons, List.not_mem_nil, or_false] at writeIn
      rcases writeIn with rfl | rfl | rfl <;> decide)
  change evaluateHOLFiniteState allocated deleteContinuation = evaluateHOLFiniteState stored countProgram at storesRun
  have countsRun := counts_execute stored frame message words.addresses words.keys words.addressCount words.keyCount empty
    storedReady.frameLocal storedReady.messageLocal storedReady.emptyGlobal countCode
    (by
      intro offset member
      apply storedReady.frameMapped
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;> decide)
    (storedReady.readsMapped (message + 152#64, words.addresses) (by simp [suffixCells]))
    (storedReady.readsStored (message + 152#64, words.addresses) (by simp [suffixCells]))
    (storedReady.readsMapped (message + 160#64, words.keys) (by simp [suffixCells]))
    (storedReady.readsStored (message + 160#64, words.keys) (by simp [suffixCells]))
    (storedReady.readsMapped (words.addresses + 24#64, words.addressCount) (by simp [suffixCells]))
    (storedReady.readsStored (words.addresses + 24#64, words.addressCount) (by simp [suffixCells]))
    (storedReady.readsMapped (words.keys + 24#64, words.keyCount) (by simp [suffixCells]))
    (storedReady.readsStored (words.keys + 24#64, words.keyCount) (by simp [suffixCells]))
    (inputAway (message + 160#64, words.keys) (by simp [suffixCells]) 264 (by decide))
    (inputAway (words.keys + 24#64, words.keyCount) (by simp [suffixCells]) 264 (by decide))
    (by change 2 ≤ source.clock - 5; omega)
  rw [countsRun] at storesRun
  change evaluateHOLFiniteState source _ =
    (let output := evaluateHOLFiniteState allocated deleteContinuation
     (output.1, restore source "del" output.2)) at tableRun
  rw [storesRun] at tableRun
  let target := restore source "del" (restore stored "acc_n"
    (emptyLocalsHOLFinite (countedFinal stored frame words.addressCount words.keyCount empty)))
  refine ⟨target, tableRun, ?_, ?_⟩
  · have clocks : source.clock - 5 - 1 - 1 = source.clock - 7 := by omega
    simp only [target, restore, emptyLocalsHOLFinite, countedFinal, countedFirst,
      WitnessRadix.QueryBranch.bind, setVarHOLFinite, stored, allocated, clocks]
  · intro query safe
    change (countedFinal stored frame words.addressCount words.keyCount empty).memory query = source.memory query
    rw [count_memory_away]
    · change WitnessRadix.WordWrites.write tableMemory _ query = source.memory query
      rw [WitnessRadix.WordWrites.write_away]
      · exact tableFrame query (delete_safe_outside lower frame scratch query safe frameAbove)
      · simp only [FieldStores.writes, deleteFields, List.map_cons, List.map_nil,
          List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨safe.2 136 (by simp [deleteStoreOffsets]), safe.2 168 (by simp [deleteStoreOffsets]), safe.2 176 (by simp [deleteStoreOffsets])⟩
    · intro offset member
      apply safe.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [deleteStoreOffsets]
theorem log_geometry (scratch lower : BitVec 64) (aligned : scratch.toNat % 8 = 0)
    (room : lower.toNat + 464 ≤ scratch.toNat) :
    ScratchList.header scratch = scratch - 24#64 ∧
    ScratchList.buffer scratch 32#64 = scratch - 56#64 ∧
    (ScratchList.header scratch).toNat = scratch.toNat - 24 ∧
    (ScratchList.buffer scratch 32#64).toNat = scratch.toNat - 56 ∧
    (ScratchList.buffer scratch 32#64).toNat % 8 = 0 ∧
    lower.toNat + 408 ≤ (ScratchList.buffer scratch 32#64).toNat := by
  have first := Arenas.rounded_decrement scratch 0 24 24 aligned (by decide) (by decide)
    (by decide) (by decide) (by omega)
  have headerEq : ScratchList.header scratch = scratch - 24#64 := by simpa [ScratchList.header] using first
  have next := Arenas.rounded_decrement scratch 24 32 32 aligned (by decide) (by decide)
    (by decide) (by decide) (by omega)
  have bufferEq : ScratchList.buffer scratch 32#64 = scratch - 56#64 := by
    simpa only [ScratchList.buffer, headerEq] using next
  have headerNumber := Arenas.cursor_number scratch 24 (by omega)
  have bufferNumber := Arenas.cursor_number scratch 56 (by omega)
  change (scratch - 24#64).toNat = _ at headerNumber
  change (scratch - 56#64).toNat = _ at bufferNumber
  refine ⟨headerEq, bufferEq, ?_, ?_, ?_, ?_⟩
  · rw [headerEq]; exact headerNumber
  · rw [bufferEq]; exact bufferNumber
  · rw [bufferEq, bufferNumber]; omega
  · rw [bufferEq, bufferNumber]; omega

/-- Three actual log/status/message stores, including EV_RUNNING at104. -/
theorem log_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message logs : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (logsLocal : source.locals.lookup (ofString "logs") = some (.val (.word logs)))
    (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (FieldStores.program "e" "msg" (logFields 0#64 0#64) continuation) =
      evaluateHOLFiniteState {source with memory := (WitnessRadix.WordWrites.write source.memory
        (FieldStores.writes frame (logFields logs message)))} continuation := by
  have reads : ∀ field ∈ logFields logs message, field.value.Ready source "msg" message := by
    intro field member
    simp only [logFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact logsLocal
    · trivial
    · exact ready.messageLocal
  have mapped : ∀ field ∈ logFields logs message, source.memaddrs (frame + BitVec.ofNat 64 field.offset) := by
    intro field member
    simp only [logFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ready.frameMapped _ (by dsimp <;> decide) (by dsimp <;> decide)
  have guarded : ∀ reader ∈ logFields logs message, ∀ writer ∈ logFields logs message,
      reader.value.Avoid message (frame + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer _
    simp only [logFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  exact FieldStores.execute source "e" "msg" frame message (logFields logs message) ready.frameLocal reads mapped guarded continuation

/-- Both actual current constructors, log/status/message stores, final
count reads and frame return consume10source ticks. All input/gas words
outside the listed stores are carried through the genuine allocations. -/
theorem logs_suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (installed : OriginalCode.Installed source.code)
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (scratchAligned : scratch.toNat%8=0) (lowerAligned : lower.toNat%8=0)
    (room : lower.toNat+464≤scratch.toNat) (frameAbove : scratch.toNat≤frame.toNat)
    (frameFits : frame.toNat+280<2^64)
    (inputsProtected : ∀ cell∈suffixCells message words,SuffixProtected lower frame cell.1)
    (logMapped : ∀ offset∈([0,8,16] : List Nat),source.memaddrs (ScratchList.header scratch+BitVec.ofNat 64 offset))
    (tableMapped : ∀ offset,offset<88 → offset%8=0 →
      source.memaddrs (ScratchPatricia.header (ScratchList.buffer scratch 32#64)+BitVec.ofNat 64 offset))
    (enough : 10≤source.clock) :
    ∃ target,evaluateHOLFiniteState source (.decCall (ofString "logs") .one (ofString "lst_new_scratch")
        [.const 8#64,.const 4#64] logContinuation)=(some (.returned (.val (.word frame))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "scratch_ptr",.val (.word (ScratchPatricia.nextScratch (ScratchList.buffer scratch 32#64))))
        memory:=target.memory
        clock:=source.clock-10} ∧
      (target.memory (frame+104#64)=.word 1#64 ∧ target.memory (frame+112#64)=.word message) ∧
      ∀ query,SuffixSafe lower frame query → target.memory query=source.memory query := by
  have logCode : source.code.lookup (ofString "lst_new_scratch")=some (ScratchList.formals,ScratchList.body,.one):=
    FrameConstruction.logs_code source.code installed
  have scratchCode:=Arenas.original_code source.code installed Arenas.Direction.down
  have geometry := log_geometry scratch lower scratchAligned room
  have amount : 8#64 * 4#64 = 32#64 := by decide
  obtain ⟨logMemory, logFrame, logRun⟩ := ScratchList.call_execute source "logs"
    [.const 8#64, .const 4#64] logContinuation scratch lower 8#64 4#64 rfl logCode scratchCode
    scratchGlobal lowerGlobal lowerAligned (by omega) (by rw [amount]; change lower.toNat + 32 ≤ (ScratchList.header scratch).toNat; rw [geometry.2.2.1]; omega) logMapped (by omega)
  rw [amount] at logRun
  let buffer := ScratchList.buffer scratch 32#64
  let allocated := WitnessRadix.QueryBranch.bind {Arenas.post source .down (ScratchList.header scratch) 32#64 with
    memory := logMemory
    clock := source.clock - 3} "logs" (ScratchList.header scratch)
  let stored := {allocated with memory := (WitnessRadix.WordWrites.write logMemory
    (FieldStores.writes frame (logFields (ScratchList.header scratch) message)))}
  have allocatedReady : SuffixReady allocated frame message words empty := by
    have changed := (ready.memory logMemory (by
      intro cell member
      exact logFrame cell.1 (suffix_protected_outside lower frame scratch cell.1 (inputsProtected cell member) frameAbove))).scratch buffer
    exact (changed.clock (source.clock - 3)).bound "logs" (ScratchList.header scratch) (by decide) (by decide)
  have storedReady : SuffixReady stored frame message words empty := by
    apply allocatedReady.stored
    intro cell member
    simp only [FieldStores.writes, logFields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    have away (offset : Nat) (inside : offset < 280) : cell.1 ≠ frame + BitVec.ofNat 64 offset :=
      suffix_protected_away lower frame cell.1 offset (inputsProtected cell member) (by omega) frameFits inside
    exact ⟨away 88 (by decide), away 104 (by decide), away 112 (by decide)⟩
  have storesRun := log_stores_execute allocated frame message (ScratchList.header scratch) words empty
    allocatedReady (bind_lookup_same _ _ _)
    (.decCall (ofString "del") .one (ofString "htab_new_scratch") [.const 20#64, .const 4#64] deleteContinuation)
  change evaluateHOLFiniteState allocated logContinuation = evaluateHOLFiniteState stored _ at storesRun
  have storedScratch : stored.globals.lookup (ofString "scratch_ptr") = some (.val (.word buffer)) := by
    simp [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, buffer, ScratchList.buffer]
  have storedLower : stored.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)) := by
    simpa [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using lowerGlobal
  obtain ⟨deleted,deleteRun,deleteFrame,deleteKept⟩:=delete_suffix_execute stored buffer lower frame message words empty
    storedReady installed storedScratch storedLower geometry.2.2.2.2.1 lowerAligned geometry.2.2.2.2.2
    (by change (ScratchList.buffer scratch 32#64).toNat≤frame.toNat; rw [geometry.2.2.2.1]; omega)
    frameFits inputsProtected tableMapped (by change 7≤source.clock-3; omega)
  rw [deleteRun] at storesRun
  change evaluateHOLFiniteState source _ =
    (let output := evaluateHOLFiniteState allocated logContinuation
     (output.1, restore source "logs" output.2)) at logRun
  rw [storesRun] at logRun
  let target := restore source "logs" deleted
  refine ⟨target, logRun, ?_, ?_, ?_⟩
  · change emptyLocalsHOLFinite deleted = _
    rw [deleteFrame]
    have overwrite : (source.globals.update (ofString "scratch_ptr", .val (.word buffer))).update
        (ofString "scratch_ptr", .val (.word (ScratchPatricia.nextScratch buffer))) =
        source.globals.update (ofString "scratch_ptr", .val (.word (ScratchPatricia.nextScratch buffer))) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
    have clocks : source.clock - 3 - 7 = source.clock - 10 := by omega
    change emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "scratch_ptr", .val (.word buffer))).update
        (ofString "scratch_ptr", .val (.word (ScratchPatricia.nextScratch buffer)))
      memory := deleted.memory
      clock := source.clock - 3 - 7} = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word (ScratchPatricia.nextScratch buffer)))
      memory := deleted.memory
      clock := source.clock - 10}
    rw [overwrite, clocks]
  · have distinct : ((FieldStores.writes frame (logFields (ScratchList.header scratch) message)).map Prod.fst).Nodup:=by
      simp [FieldStores.writes,logFields,BitVec.add_right_inj]
    constructor
    · change deleted.memory (frame+104#64)=.word 1#64
      rw [deleteKept _ (delete_link_safe lower frame 104 (by simp) frameFits)]
      exact WordWrites.write_unique logMemory _ (frame+104#64,1#64) distinct
        (by simp [FieldStores.writes,logFields,FieldStores.Value.word])
    · change deleted.memory (frame+112#64)=.word message
      rw [deleteKept _ (delete_link_safe lower frame 112 (by simp) frameFits)]
      exact WordWrites.write_unique logMemory _ (frame+112#64,message) distinct
        (by simp [FieldStores.writes,logFields,FieldStores.Value.word])
  · intro query safe
    change deleted.memory query = source.memory query
    rw [deleteKept query (DeleteSafe.of_suffix safe)]
    change WitnessRadix.WordWrites.write logMemory _ query = source.memory query
    rw [WitnessRadix.WordWrites.write_away]
    · exact logFrame query (suffix_safe_outside lower frame scratch query safe frameAbove)
    · simp only [FieldStores.writes, logFields, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨safe.2 88 (by simp [suffixStoreOffsets]), safe.2 104 (by simp [suffixStoreOffsets]), safe.2 112 (by simp [suffixStoreOffsets])⟩
theorem bitmap_geometry (scratch lower length : BitVec 64)
    (aligned : scratch.toNat % 8 = 0) (fits : length.toNat + 63 < 2 ^ 64)
    (room : lower.toNat + JumpDest.bitmapBytes length.toNat + 464 ≤ scratch.toNat) :
    Arenas.rounded .down scratch (JumpDest.bytesWord length) =
        scratch - BitVec.ofNat 64 (JumpDest.bitmapBytes length.toNat) ∧
    (Arenas.rounded .down scratch (JumpDest.bytesWord length)).toNat = scratch.toNat - JumpDest.bitmapBytes length.toNat ∧
    (Arenas.rounded .down scratch (JumpDest.bytesWord length)).toNat % 8 = 0 ∧
    lower.toNat + 464 ≤ (Arenas.rounded .down scratch (JumpDest.bytesWord length)).toNat := by
  have bytes := JumpDest.bytes_number length fits
  have geometry := JumpDest.bytes_geometry length.toNat
  have exactWord : JumpDest.bytesWord length = BitVec.ofNat 64 (JumpDest.bitmapBytes length.toNat) := by
    rw [← bytes]
    simp
  have roundEq := Arenas.rounded_decrement scratch 0 (JumpDest.bitmapBytes length.toNat)
    (JumpDest.bitmapBytes length.toNat) aligned (by decide) geometry.1 (by omega) (by omega) (by omega)
  simp only [BitVec.sub_zero, Nat.zero_add] at roundEq
  have pointerEq : Arenas.rounded .down scratch (JumpDest.bytesWord length) =
      scratch - BitVec.ofNat 64 (JumpDest.bitmapBytes length.toNat) := by rw [exactWord]; exact roundEq
  have number := Arenas.cursor_number scratch (JumpDest.bitmapBytes length.toNat) (by omega)
  refine ⟨pointerEq, ?_, ?_, ?_⟩
  · rw [pointerEq]; exact number
  · rw [pointerEq, number]; omega
  · rw [pointerEq, number]; omega

/-- Full actual frame suffix, from code scan through the real return.
Every constructor and count read executes, actual dynamic cursor/clock state
is retained, and all regular-ledger cells survive. -/
theorem suffix_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64)
    (ready : SuffixReady source frame message words empty)
    (installed : OriginalCode.Installed source.code)
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word lower)))
    (scratchAligned : scratch.toNat%8=0) (lowerAligned : lower.toNat%8=0)
    (lengthFits : words.length.toNat+63<2^64)
    (room : lower.toNat+JumpDest.bitmapBytes words.length.toNat+464≤scratch.toNat)
    (frameAbove : scratch.toNat≤frame.toNat) (frameFits : frame.toNat+280<2^64)
    (inputsProtected : ∀ cell∈suffixCells message words,SuffixProtected lower frame cell.1)
    (codeMapped : ∀ offset<words.length.toNat,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress words.code offset)))
    (bitmapMapped : ∀ offset,offset+8≤JumpDest.bitmapBytes words.length.toNat → offset%8=0 →
      source.memaddrs (byteAddress (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) offset))
    (logMapped : ∀ offset∈([0,8,16] : List Nat),source.memaddrs
      (ScratchList.header (Arenas.rounded .down scratch (JumpDest.bytesWord words.length))+BitVec.ofNat 64 offset))
    (tableMapped : ∀ offset,offset<88 → offset%8=0 → source.memaddrs
      (ScratchPatricia.header (ScratchList.buffer (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) 32#64)+BitVec.ofNat 64 offset))
    (enough : words.length.toNat+Zero.price (JumpDest.bitmapBytes words.length.toNat)+13≤source.clock) :
    ∃ target spent,spent≤words.length.toNat ∧ evaluateHOLFiniteState source afterGas=(some (.returned (.val (.word frame))),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "scratch_ptr",.val (.word
          (ScratchPatricia.nextScratch (ScratchList.buffer (Arenas.rounded .down scratch (JumpDest.bytesWord words.length)) 32#64))))
        memory:=target.memory
        clock:=source.clock-(Zero.price (JumpDest.bitmapBytes words.length.toNat)+13+spent)} ∧
      regularBudget target.memory frame=regularBudget source.memory frame ∧
      (target.memory (frame+104#64)=.word 1#64 ∧ target.memory (frame+112#64)=.word message) ∧
      ∀ query,SuffixSafe lower frame query → target.memory query=source.memory query := by
  have jumpCode:=FrameConstruction.jump_code source.code installed
  have scratchCode:=Arenas.original_code source.code installed Arenas.Direction.down
  have zeroCode:=Zero.original_code source.code installed
  let bitmap := Arenas.rounded .down scratch (JumpDest.bytesWord words.length)
  let price := WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat)
  have geometry := bitmap_geometry scratch lower words.length scratchAligned lengthFits room
  have codeRead := FieldStores.Value.read source "msg" message (.copied 112 words.code)
    (ready.copied 112 words.code (by simp [suffixCells]))
  have lengthRead := FieldStores.Value.read source "msg" message (.copied 120 words.length)
    (ready.copied 120 words.length (by simp [suffixCells]))
  simp only [FieldStores.Value.expression, FieldStores.Value.word, eval] at codeRead lengthRead
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [messageLoad 112, messageLoad 120] = some (JumpDest.values words.code words.length) := by
    simp only [evalListHOLFinite, evalListHOLExact, messageLoad, codeRead, lengthRead, JumpDest.values]
  obtain ⟨bitmapMemory, spent, spentBound, bitmapFrame, bitmapRun⟩ := JumpDest.call_execute source "jd"
    [messageLoad 112, messageLoad 120] jumpContinuation scratch lower words.code words.length args
    jumpCode scratchCode zeroCode scratchGlobal lowerGlobal lowerAligned lengthFits (by omega)
    codeMapped bitmapMapped (by omega)
  let allocated := WitnessRadix.QueryBranch.bind {Arenas.post source .down scratch (JumpDest.bytesWord words.length) with
    memory := bitmapMemory
    clock := source.clock - (price + 3 + spent)} "jd" bitmap
  let stored := {allocated with memory := (WitnessRadix.WordWrites.write bitmapMemory (FieldStores.writes frame (jumpFields bitmap)))}
  have allocatedReady : SuffixReady allocated frame message words empty := by
    have changed := (ready.memory bitmapMemory (by
      intro cell member
      exact bitmapFrame cell.1 (suffix_protected_outside lower frame scratch cell.1 (inputsProtected cell member) frameAbove))).scratch bitmap
    exact (changed.clock (source.clock - (price + 3 + spent))).bound "jd" bitmap (by decide) (by decide)
  have storedReady : SuffixReady stored frame message words empty := by
    apply allocatedReady.stored
    intro cell member
    simpa [FieldStores.writes, jumpFields] using
      suffix_protected_away lower frame cell.1 80 (inputsProtected cell member) (by omega) frameFits (by decide)
  have storesRun := FieldStores.execute allocated "e" "msg" frame message (jumpFields bitmap)
    allocatedReady.frameLocal
    (by intro field member; simp only [jumpFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst field; exact bind_lookup_same _ _ _)
    (by intro field member; simp only [jumpFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst field; exact allocatedReady.frameMapped 80 (by decide) (by decide))
    (by intro reader member writer _; simp only [jumpFields, List.mem_cons, List.not_mem_nil, or_false] at member; subst reader; trivial)
    (.decCall (ofString "logs") .one (ofString "lst_new_scratch") [.const 8#64, .const 4#64] logContinuation)
  change evaluateHOLFiniteState allocated jumpContinuation = evaluateHOLFiniteState stored _ at storesRun
  have storedScratch : stored.globals.lookup (ofString "scratch_ptr") = some (.val (.word bitmap)) := by
    simp [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, bitmap]
  have storedLower : stored.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)) := by
    simpa [stored, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using lowerGlobal
  obtain ⟨logged,logsRun,logsFrame,logsLinks,logsKept⟩:=logs_suffix_execute stored bitmap lower frame message words empty
    storedReady installed storedScratch storedLower geometry.2.2.1 lowerAligned geometry.2.2.2
    (by change bitmap.toNat≤frame.toNat; dsimp [bitmap]; rw [geometry.2.1]; omega)
    frameFits inputsProtected logMapped tableMapped
    (by change 10≤source.clock-(price+3+spent); dsimp [price]; omega)
  rw [logsRun] at storesRun
  change evaluateHOLFiniteState source suffixProgram =
    (let output := evaluateHOLFiniteState allocated jumpContinuation
     (output.1, restore source "jd" output.2)) at bitmapRun
  rw [storesRun] at bitmapRun
  let target := restore source "jd" logged
  have kept (query : BitVec 64) (safe : SuffixSafe lower frame query) : target.memory query = source.memory query := by
    change logged.memory query = source.memory query
    rw [logsKept query safe]
    change WitnessRadix.WordWrites.write bitmapMemory _ query = source.memory query
    rw [WitnessRadix.WordWrites.write_away]
    · exact bitmapFrame query (suffix_safe_outside lower frame scratch query safe frameAbove)
    · simpa [FieldStores.writes, jumpFields] using safe.2 80 (by simp [suffixStoreOffsets])
  refine ⟨target, spent, spentBound, ?_, ?_, ?_, logsLinks, kept⟩
  · rw [actual_suffix]
    exact bitmapRun
  · change emptyLocalsHOLFinite logged = _
    rw [logsFrame]
    let lastCursor := ScratchPatricia.nextScratch (ScratchList.buffer bitmap 32#64)
    have overwrite : (source.globals.update (ofString "scratch_ptr", .val (.word bitmap))).update
        (ofString "scratch_ptr", .val (.word lastCursor)) =
        source.globals.update (ofString "scratch_ptr", .val (.word lastCursor)) := by
      apply HolFiniteMapExact.ext
      funext query
      by_cases same : ofString "scratch_ptr" = query <;> simp [HolFiniteMapExact.update, FUPDATE, same]
    have clocks : source.clock - (price + 3 + spent) - 10 = source.clock - (price + 13 + spent) := by omega
    change emptyLocalsHOLFinite {source with
      globals := (source.globals.update (ofString "scratch_ptr", .val (.word bitmap))).update
        (ofString "scratch_ptr", .val (.word lastCursor))
      memory := logged.memory
      clock := source.clock - (price + 3 + spent) - 10} = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "scratch_ptr", .val (.word lastCursor))
      memory := logged.memory
      clock := source.clock - (price + 13 + spent)}
    rw [overwrite, clocks]
  · have preserved (offset : Nat) (member : offset ∈ ([64, 184, 192] : List Nat)) :=
      kept (frame + BitVec.ofNat 64 offset) (suffix_regular_safe lower frame offset member frameFits)
    simp only [regularBudget, wordAt, preserved 64 (by simp), preserved 184 (by simp), preserved 192 (by simp)]

/-- Every external suffix read is genuinely mapped, holds its observed word,
and lies below the frame arena. Both zero counts come from the constructed
current warm-table images. -/
theorem first_inputs {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (words : MessageWords)
    (codeCell : source.memory (message+112#64)=.word words.code)
    (lengthCell : source.memory (message+120#64)=.word words.length) :
    ∀ cell∈suffixCells message ⟨words.code,words.length,accounts,storage,0#64,0#64⟩,
      source.memaddrs cell.1 ∧ source.memory cell.1=.word cell.2 ∧ cell.1.toNat<2952790016 := by
  obtain ⟨messageOrder,accountOrder,storageBound⟩:=FrameConstruction.memory_layout state
  have messageBound : message.toNat+176≤2952790016:=by omega
  have accountBound : accounts.toNat+88≤2952790016:=by omega
  have messageRead (offset : Nat) (value : BitVec 64) (inside : offset<176) (aligned : offset%8=0)
      (stored : source.memory (message+BitVec.ofNat 64 offset)=.word value) :
      source.memaddrs (message+BitVec.ofNat 64 offset) ∧ source.memory (message+BitVec.ofNat 64 offset)=.word value ∧
        (message+BitVec.ofNat 64 offset).toNat<2952790016 := by
    refine ⟨AllocatedBytes.word_mapped source message 176 offset state.environment.arena.domain state.messageArena inside state.messageAligned aligned,stored,?_⟩
    have number : (message+BitVec.ofNat 64 offset).toNat=message.toNat+offset:=byteAddress_toNat message offset (by omega)
    rw [number]
    omega
  have accountRead : source.memaddrs (accounts+24#64) ∧ source.memory (accounts+24#64)=.word 0#64 ∧ (accounts+24#64).toNat<2952790016 := by
    refine ⟨AllocatedBytes.word_mapped source accounts 88 24 state.environment.arena.domain state.accountsImage.geometry.table
      (by decide) state.accountsImage.aligned (by decide),?_,?_⟩
    · exact state.accountsImage.fields (accounts+24#64,0#64) (by simp [CurrentTable.New.scalarWrites])
    · have number : (accounts+24#64).toNat=accounts.toNat+24:=byteAddress_toNat accounts 24 (by omega)
      rw [number]; omega
  have storageRead : source.memaddrs (storage+24#64) ∧ source.memory (storage+24#64)=.word 0#64 ∧ (storage+24#64).toNat<2952790016 := by
    refine ⟨AllocatedBytes.word_mapped source storage 88 24 state.environment.arena.domain state.storageImage.geometry.table
      (by decide) state.storageImage.aligned (by decide),?_,?_⟩
    · exact state.storageImage.fields (storage+24#64,0#64) (by simp [CurrentTable.New.scalarWrites])
    · have number : (storage+24#64).toNat=storage.toNat+24:=byteAddress_toNat storage 24 (by omega)
      rw [number]; omega
  intro cell member
  simp only [suffixCells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  · exact messageRead 112 words.code (by decide) (by decide) codeCell
  · exact messageRead 120 words.length (by decide) (by decide) lengthCell
  · exact messageRead 152 accounts (by decide) (by decide) state.accountsCell
  · exact messageRead 160 storage (by decide) (by decide) state.storageCell
  · exact accountRead
  · exact storageRead

/-- All real initial-frame suffix conditions concerning message, access
counts, empty-buffer global and frame slots are derived through the actual
17-tick prefix. This does not retain fixed startup cursors after allocation. -/
theorem first_ready {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (messageCell : source.locals.lookup (ofString "msg")=some (.val (.word message)))
    (words : MessageWords)
    (codeCell : source.memory (message+112#64)=.word words.code)
    (lengthCell : source.memory (message+120#64)=.word words.length) :
    ∃ empty,SuffixReady (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words)
        FrameConstruction.frameStart message ⟨words.code,words.length,accounts,storage,0#64,0#64⟩ empty ∧
      ∀ cell∈suffixCells message ⟨words.code,words.length,accounts,storage,0#64,0#64⟩,
        SuffixProtected FrameConstruction.memoryNext FrameConstruction.frameStart cell.1 := by
  let suffixWords : SuffixWords:=⟨words.code,words.length,accounts,storage,0#64,0#64⟩
  have inputs:=first_inputs state words codeCell lengthCell
  obtain ⟨empty,emptyCell⟩:=state.empty_global
  have frameMapped : ∀ offset,offset+8≤280 → offset%8=0 → source.memaddrs (byteAddress FrameConstruction.frameStart offset) := by
    intro offset inside aligned
    exact AllocatedBytes.word_mapped source FrameConstruction.frameStart 280 offset state.environment.arena.domain
      ⟨by decide,by decide⟩ (by omega) (by decide) aligned
  have separated : ∀ cell∈suffixCells message suffixWords,∀ offset<280,cell.1≠byteAddress FrameConstruction.frameStart offset := by
    intro cell member offset inside same
    have bound:=(inputs cell member).2.2
    have number:=byteAddress_toNat FrameConstruction.frameStart offset (by change 2965298920+offset<2^64; omega)
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    change cell.1.toNat=2965298920+offset at equal
    omega
  refine ⟨empty,fresh_suffix_ready source FrameConstruction.scratchStart FrameConstruction.memoryStart message empty words suffixWords messageCell emptyCell frameMapped
    (fun cell member=>(inputs cell member).1) (fun cell member=>(inputs cell member).2.1) separated,?_⟩
  intro cell member
  apply Or.inl
  have bound:=(inputs cell member).2.2
  change cell.1.toNat<2952791040
  omega

/-- The real bounded code length and initial arena cursors derive every
bitmap/log/current-Patricia header mapping. No mapped-buffer premise is added
at the actual first constructor entry. -/
theorem first_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bytes : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (bound : bytes.toNat≤65536) :
    (∀ offset,offset+8≤JumpDest.bitmapBytes bytes.toNat → offset%8=0 → source.memaddrs
      (byteAddress (Arenas.rounded .down FrameConstruction.stackStart (JumpDest.bytesWord bytes)) offset)) ∧
    (∀ offset∈([0,8,16] : List Nat),source.memaddrs
      (ScratchList.header (Arenas.rounded .down FrameConstruction.stackStart (JumpDest.bytesWord bytes))+BitVec.ofNat 64 offset)) ∧
    (∀ offset,offset<88 → offset%8=0 → source.memaddrs
      (ScratchPatricia.header (ScratchList.buffer (Arenas.rounded .down FrameConstruction.stackStart (JumpDest.bytesWord bytes)) 32#64)+BitVec.ofNat 64 offset)) := by
  let bitmap:=Arenas.rounded .down FrameConstruction.stackStart (JumpDest.bytesWord bytes)
  let buffer:=ScratchList.buffer bitmap 32#64
  have sizeBound:=FrameConstruction.bitmap_bound bound
  have fits : bytes.toNat+63<2^64:=by omega
  have room : FrameConstruction.memoryNext.toNat+JumpDest.bitmapBytes bytes.toNat+464≤FrameConstruction.stackStart.toNat := by
    change 2952791040+JumpDest.bitmapBytes bytes.toNat+464≤2965297896
    omega
  have bitmapGeometry:=bitmap_geometry FrameConstruction.stackStart FrameConstruction.memoryNext bytes (by decide) fits room
  have bitmapNumber : bitmap.toNat=2965297896-JumpDest.bitmapBytes bytes.toNat:=bitmapGeometry.2.1
  have bitmapRoom : 2952791040+464≤bitmap.toNat:=bitmapGeometry.2.2.2
  have logGeometry:=log_geometry bitmap FrameConstruction.memoryNext bitmapGeometry.2.2.1 bitmapGeometry.2.2.2
  have logNumber : (ScratchList.header bitmap).toNat=bitmap.toNat-24:=logGeometry.2.2.1
  have bufferNumber : buffer.toNat=bitmap.toNat-56:=logGeometry.2.2.2.1
  have bufferRoom : 2952791040+408≤buffer.toNat:=logGeometry.2.2.2.2.2
  have tableGeometry:=ScratchPatricia.geometry buffer logGeometry.2.2.2.2.1 (by omega)
  have tableNumber:=tableGeometry.headerNumber
  have bitmapArena : AllocatedBytes.Arena bitmap (JumpDest.bitmapBytes bytes.toNat):=⟨by omega,by omega⟩
  have logArena : AllocatedBytes.Arena (ScratchList.header bitmap) 24:=⟨by omega,by omega⟩
  have tableArena : AllocatedBytes.Arena (ScratchPatricia.header buffer) 88:=⟨by omega,by omega⟩
  refine ⟨?_,?_,?_⟩
  · intro offset inside aligned
    exact AllocatedBytes.word_mapped source bitmap _ offset domain bitmapArena (by omega) bitmapGeometry.2.2.1 aligned
  · intro offset member
    have inside : offset<24:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> decide
    have aligned : offset%8=0:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> decide
    have headerAligned : (ScratchList.header bitmap).toNat%8=0:=by
      rw [logNumber]
      have aligned:=bitmapGeometry.2.2.1
      omega
    exact AllocatedBytes.word_mapped source _ _ offset domain logArena inside headerAligned aligned
  · intro offset inside aligned
    exact AllocatedBytes.word_mapped source _ _ offset domain tableArena inside tableGeometry.headerAligned aligned

/-- The real280-byte clear and subsequent initialization derive the exact
three regular-gas cells. This minimal statement is independent of the old
VM proof umbrella and its obsolete scratch-table imports. -/
theorem first_fresh_seed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : MessageWords) :
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).memory (FrameConstruction.frameStart+64#64)=.word words.gas ∧
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).memory (FrameConstruction.frameStart+184#64)=.word 0#64 ∧
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).memory (FrameConstruction.frameStart+192#64)=.word 0#64 ∧
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).memory (FrameConstruction.frameStart+72#64)=.word words.reservoir := by
  let cleared:=zeroed source FrameConstruction.scratchStart FrameConstruction.memoryStart
  let allocated:=memoryAllocated cleared FrameConstruction.frameStart FrameConstruction.memoryStart FrameConstruction.scratchStart
  have used : allocated.memory (FrameConstruction.frameStart+184#64)=.word 0#64 := by
    rw [allocation_memory_away]
    · exact zeroed_cell source FrameConstruction.scratchStart FrameConstruction.memoryStart 23 (by decide)
    · simp [FieldStores.writes,stackFields,BitVec.add_right_inj]
  have spill : allocated.memory (FrameConstruction.frameStart+192#64)=.word 0#64 := by
    rw [allocation_memory_away]
    · exact zeroed_cell source FrameConstruction.scratchStart FrameConstruction.memoryStart 24 (by decide)
    · simp [FieldStores.writes,stackFields,BitVec.add_right_inj]
  have distinct : ((FieldStores.writes FrameConstruction.frameStart (fields FrameConstruction.memoryStart FrameConstruction.memoryStart words)).map Prod.fst).Nodup := by
    simp [FieldStores.writes,fields,BitVec.add_right_inj]
  unfold fresh
  rw [show Arenas.rounded .down FrameConstruction.scratchStart 280#64=FrameConstruction.frameStart from by decide]
  change WordWrites.write allocated.memory (FieldStores.writes FrameConstruction.frameStart (fields FrameConstruction.memoryStart FrameConstruction.memoryStart words)) (FrameConstruction.frameStart+64#64)=.word words.gas ∧
    WordWrites.write allocated.memory (FieldStores.writes FrameConstruction.frameStart (fields FrameConstruction.memoryStart FrameConstruction.memoryStart words)) (FrameConstruction.frameStart+184#64)=.word 0#64 ∧
    WordWrites.write allocated.memory (FieldStores.writes FrameConstruction.frameStart (fields FrameConstruction.memoryStart FrameConstruction.memoryStart words)) (FrameConstruction.frameStart+192#64)=.word 0#64 ∧
    WordWrites.write allocated.memory (FieldStores.writes FrameConstruction.frameStart (fields FrameConstruction.memoryStart FrameConstruction.memoryStart words)) (FrameConstruction.frameStart+72#64)=.word words.reservoir
  refine ⟨WordWrites.write_unique allocated.memory _ (FrameConstruction.frameStart+64#64,words.gas) distinct
    (by simp [FieldStores.writes,fields,FieldStores.Value.word]),?_,?_,?_⟩
  · rw [WordWrites.write_away]
    · exact used
    · simp [FieldStores.writes,fields,BitVec.add_right_inj]
  · rw [WordWrites.write_away]
    · exact spill
    · simp [FieldStores.writes,fields,BitVec.add_right_inj]
  · exact WordWrites.write_unique allocated.memory _ (FrameConstruction.frameStart+72#64,words.reservoir) distinct
      (by simp [FieldStores.writes,fields,FieldStores.Value.word])

/-- The actual message-to-frame stores write the original code pointer
and length before any scan. Both cells are outside the later suffix writes. -/
theorem first_fresh_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : MessageWords) :
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).memory (FrameConstruction.frameStart+48#64)=.word words.code ∧
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).memory (FrameConstruction.frameStart+56#64)=.word words.length := by
  let allocated:=memoryAllocated (zeroed source FrameConstruction.scratchStart FrameConstruction.memoryStart)
    FrameConstruction.frameStart FrameConstruction.memoryStart FrameConstruction.scratchStart
  have distinct : ((FieldStores.writes FrameConstruction.frameStart (fields FrameConstruction.memoryStart FrameConstruction.memoryStart words)).map Prod.fst).Nodup:=by
    simp [FieldStores.writes,fields,BitVec.add_right_inj]
  unfold fresh
  rw [show Arenas.rounded .down FrameConstruction.scratchStart 280#64=FrameConstruction.frameStart from by decide]
  constructor
  · exact WordWrites.write_unique allocated.memory _ (FrameConstruction.frameStart+48#64,words.code) distinct
      (by simp [FieldStores.writes,fields,FieldStores.Value.word])
  · exact WordWrites.write_unique allocated.memory _ (FrameConstruction.frameStart+56#64,words.length) distinct
      (by simp [FieldStores.writes,fields,FieldStores.Value.word])

theorem first_fresh_global (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : MessageWords) (key : MlS)
    (notScratch : key≠ofString "scratch_ptr") (notFrame : key≠ofString "frame_mem_ptr") :
    (fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words).globals.lookup key=source.globals.lookup key := by
  simp [fresh,initialized,memoryAllocated,stackInitialized,stackAllocated,zeroed,allocated,markedMemory,markedScratch,Arenas.post,Arenas.pointerName,
    QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notScratch,Ne.symm notFrame]

/-- The complete actual first frame constructor, with its normal result,
source clocks, gas ledger, dynamic cursors and persistent-memory frame all
derived from the already constructed message. No future execution or extra
allocation/ownership assumption appears at this entry. -/
theorem first_execute {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (messageCell : source.locals.lookup (ofString "msg")=some (.val (.word message)))
    (enough : FrameConstruction.bodyPrice≤source.clock) :
    ∃ bytes spent post,bytes≤65536 ∧ spent≤bytes ∧
      evaluateHOLFiniteState source FrameConstruction.body=(some (.returned (.val (.word FrameConstruction.frameStart))),post) ∧
      post.clock=source.clock-(Zero.price (JumpDest.bitmapBytes bytes)+30+spent) ∧
      regularBudget post.memory FrameConstruction.frameStart=30000000 ∧
      (post.memory (FrameConstruction.frameStart+64#64)=.word 30000000#64 ∧
        post.memory (FrameConstruction.frameStart+184#64)=.word 0#64 ∧ post.memory (FrameConstruction.frameStart+192#64)=.word 0#64 ∧
        post.memory (FrameConstruction.frameStart+72#64)=.word 1566720#64) ∧
      post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word FrameConstruction.memoryNext)) ∧
      (∃ cursor,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) ∧ cursor.toNat%8=0 ∧
        cursor.toNat=2965297896-JumpDest.bitmapBytes bytes-464 ∧ FrameConstruction.memoryNext.toNat≤cursor.toNat) ∧
      (∀ key,key≠ofString "scratch_ptr" → key≠ofString "frame_mem_ptr" → post.globals.lookup key=source.globals.lookup key) ∧
      OriginalScalarGlobals.Scalars post.globals ∧
      (post.memory (FrameConstruction.frameStart+104#64)=.word 1#64 ∧ post.memory (FrameConstruction.frameStart+112#64)=.word message) ∧
      (post.memory (FrameConstruction.frameStart+48#64)=source.memory (message+112#64) ∧
        post.memory (FrameConstruction.frameStart+56#64)=source.memory (message+120#64)) ∧
      ∀ query,Arenas.Outside FrameConstruction.memoryStart FrameConstruction.scratchStart query → post.memory query=source.memory query := by
  obtain ⟨words,gasCell,reservoirCell,bound,codeArena,pointerCell,bytesCell,prefixRun⟩:=FrameConstruction.actual_prefix state messageCell
    (by unfold FrameConstruction.bodyPrice at enough; omega)
  let freshState:=fresh source FrameConstruction.scratchStart FrameConstruction.memoryStart words
  let suffixWords : SuffixWords:=⟨words.code,words.length,accounts,storage,0#64,0#64⟩
  obtain ⟨empty,ready,inputsProtected⟩:=first_ready state messageCell words pointerCell bytesCell
  have freshClock : freshState.clock=source.clock-17:=(fresh_budget source FrameConstruction.scratchStart FrameConstruction.memoryStart words).2
  have installed : OriginalCode.Installed freshState.code:=state.environment.arena.code
  have domain : freshState.memaddrs=InitE.ordinaryDomain:=state.environment.arena.domain
  have scratchCell : freshState.globals.lookup (ofString "scratch_ptr")=some (.val (.word FrameConstruction.stackStart)) := by
    simp [freshState,fresh,initialized,memoryAllocated,stackInitialized,stackAllocated,zeroed,allocated,
      Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    decide
  have lowerCell : freshState.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word FrameConstruction.memoryNext)) := by
    simp [freshState,fresh,initialized,memoryAllocated,Arenas.post,Arenas.pointerName,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    decide
  have maps:=first_mapped freshState words.length domain bound
  have fits : words.length.toNat+63<2^64:=by omega
  have bitmapBound:=FrameConstruction.bitmap_bound bound
  have room : FrameConstruction.memoryNext.toNat+JumpDest.bitmapBytes words.length.toNat+464≤FrameConstruction.stackStart.toNat := by
    change 2952791040+JumpDest.bitmapBytes words.length.toNat+464≤2965297896
    omega
  have codeMapped : ∀ offset<words.length.toNat,freshState.memaddrs (panByteAlignHOL (width:=64) (byteAddress words.code offset)) := by
    intro offset inside
    rcases codeArena with zero|arena
    · rw [zero] at inside; change offset<0 at inside; omega
    · exact AllocatedBytes.byte_mapped freshState words.code words.length.toNat offset domain arena inside
  have suffixClock : words.length.toNat+Zero.price (JumpDest.bitmapBytes words.length.toNat)+13≤freshState.clock := by
    have maximum:=FrameConstruction.body_price_bound bound
    unfold FrameConstruction.bodyPrice at enough maximum
    rw [freshClock]
    omega
  obtain ⟨suffixPost,spent,spentBound,suffixRun,suffixFrame,budget,links,preserved⟩:=suffix_execute freshState FrameConstruction.stackStart FrameConstruction.memoryNext
    FrameConstruction.frameStart message suffixWords empty ready installed scratchCell lowerCell (by decide) (by decide) fits room
    (by decide) (by decide) inputsProtected codeMapped maps.1 maps.2.1 maps.2.2 suffixClock
  rw [suffixRun] at prefixRun
  let post:=freshRestore source FrameConstruction.scratchStart FrameConstruction.memoryStart suffixPost
  have actual : evaluateHOLFiniteState source FrameConstruction.body=(some (.returned (.val (.word FrameConstruction.frameStart))),post):=prefixRun
  have clock:=congrArg PanSemStateFiniteExact.clock suffixFrame
  change suffixPost.clock=freshState.clock-(Zero.price (JumpDest.bitmapBytes words.length.toNat)+13+spent) at clock
  have globals:=congrArg PanSemStateFiniteExact.globals suffixFrame
  let bitmap:=Arenas.rounded .down FrameConstruction.stackStart (JumpDest.bytesWord words.length)
  let buffer:=ScratchList.buffer bitmap 32#64
  let lastCursor:=ScratchPatricia.nextScratch buffer
  change suffixPost.globals=freshState.globals.update (ofString "scratch_ptr",.val (.word lastCursor)) at globals
  have lowerPost : post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word FrameConstruction.memoryNext)) := by
    change suffixPost.globals.lookup (ofString "frame_mem_ptr")=_
    rw [globals]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using lowerCell
  have cursorPost : post.globals.lookup (ofString "scratch_ptr")=some (.val (.word lastCursor)) := by
    change suffixPost.globals.lookup (ofString "scratch_ptr")=_
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  have bitmapGeometry:=bitmap_geometry FrameConstruction.stackStart FrameConstruction.memoryNext words.length (by decide) fits room
  have logGeometry:=log_geometry bitmap FrameConstruction.memoryNext bitmapGeometry.2.2.1 bitmapGeometry.2.2.2
  have bufferRoom : 2952791040+408≤buffer.toNat:=logGeometry.2.2.2.2.2
  have tableGeometry:=ScratchPatricia.geometry buffer logGeometry.2.2.2.2.1 (by omega)
  have cursorLower : FrameConstruction.memoryNext.toNat≤lastCursor.toNat := by
    have before:=logGeometry.2.2.2.2.2
    have number:=tableGeometry.nextNumber
    change 2952791040≤(ScratchPatricia.nextScratch buffer).toNat
    omega
  have cursorNumber : lastCursor.toNat=2965297896-JumpDest.bitmapBytes words.length.toNat-464 := by
    have bitmapNumber : bitmap.toNat=2965297896-JumpDest.bitmapBytes words.length.toNat:=bitmapGeometry.2.1
    have bufferNumber : buffer.toNat=bitmap.toNat-56:=logGeometry.2.2.2.1
    have lastNumber : lastCursor.toNat=buffer.toNat-408:=tableGeometry.nextNumber
    omega
  have noncursor : ∀ key,key≠ofString "scratch_ptr" → key≠ofString "frame_mem_ptr" → post.globals.lookup key=source.globals.lookup key := by
    intro key notScratch notFrame
    change suffixPost.globals.lookup key=_
    rw [globals]
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm notScratch] using first_fresh_global source words key notScratch notFrame
  have seed:=first_fresh_seed source words
  have kept (offset : Nat) (member : offset∈([64,184,192] : List Nat)) :
      post.memory (FrameConstruction.frameStart+BitVec.ofNat 64 offset)=freshState.memory (FrameConstruction.frameStart+BitVec.ofNat 64 offset) :=
    preserved _ (suffix_regular_safe FrameConstruction.memoryNext FrameConstruction.frameStart offset member (by decide))
  have stateSafe : SuffixSafe FrameConstruction.memoryNext FrameConstruction.frameStart (FrameConstruction.frameStart+72#64):=
    ⟨Or.inr (by decide),by simp [suffixStoreOffsets,BitVec.add_right_inj]⟩
  have stateKept : post.memory (FrameConstruction.frameStart+72#64)=freshState.memory (FrameConstruction.frameStart+72#64):=preserved _ stateSafe
  have finalSeed : post.memory (FrameConstruction.frameStart+64#64)=.word 30000000#64 ∧
      post.memory (FrameConstruction.frameStart+184#64)=.word 0#64 ∧ post.memory (FrameConstruction.frameStart+192#64)=.word 0#64 ∧
      post.memory (FrameConstruction.frameStart+72#64)=.word 1566720#64 :=
    ⟨(kept 64 (by simp)).trans (by rw [gasCell] at seed; exact seed.1),
      (kept 184 (by simp)).trans seed.2.1,(kept 192 (by simp)).trans seed.2.2.1,
      stateKept.trans (by rw [reservoirCell] at seed; exact seed.2.2.2)⟩
  have codeFields:=first_fresh_code source words
  have code48 : post.memory (FrameConstruction.frameStart+48#64)=source.memory (message+112#64):=
    (preserved _ ⟨Or.inr (by decide),by simp [suffixStoreOffsets,BitVec.add_right_inj]⟩).trans (codeFields.1.trans pointerCell.symm)
  have code56 : post.memory (FrameConstruction.frameStart+56#64)=source.memory (message+120#64):=
    (preserved _ ⟨Or.inr (by decide),by simp [suffixStoreOffsets,BitVec.add_right_inj]⟩).trans (codeFields.2.trans bytesCell.symm)
  refine ⟨words.length.toNat,spent,post,bound,spentBound,actual,?_,?_,finalSeed,lowerPost,⟨lastCursor,cursorPost,tableGeometry.nextAligned,cursorNumber,cursorLower⟩,noncursor,
    state.environment.arena.scalars.after actual,links,⟨code48,code56⟩,?_⟩
  · change suffixPost.clock=source.clock-_
    rw [clock,freshClock]
    omega
  · exact budget.trans ((fresh_budget source FrameConstruction.scratchStart FrameConstruction.memoryStart words).1.trans (by rw [gasCell]; rfl))
  · intro query outside
    have protectedRead : SuffixProtected FrameConstruction.memoryNext FrameConstruction.frameStart query := by
      rcases outside with below|above
      · apply Or.inl
        change query.toNat<2952790016 at below
        change query.toNat<2952791040
        omega
      · apply Or.inr
        change 2965299200≤query.toNat at above
        change 2965298920+280≤query.toNat
        omega
    change suffixPost.memory query=source.memory query
    rw [preserved query (suffix_protected_safe FrameConstruction.memoryNext FrameConstruction.frameStart query protectedRead (by decide) (by decide))]
    apply fresh_memory_away
    intro offset inside same
    have number:=byteAddress_toNat FrameConstruction.frameStart offset
      (by change offset<280 at inside; change 2965298920+offset<2^64; omega)
    have equal:=congrArg BitVec.toNat same
    rw [show Arenas.rounded .down FrameConstruction.scratchStart 280#64=FrameConstruction.frameStart from by decide] at equal
    rw [number] at equal
    change query.toNat=2965298920+offset at equal
    rcases outside with below|above
    · change query.toNat<2952790016 at below; omega
    · change 2965299200≤query.toNat at above; change offset<280 at inside; omega

end InitECandidate.Solver.Input.CurrentVerify.FrameNormal

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.delete_stores_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.delete_suffix_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.log_geometry
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.log_stores_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.logs_suffix_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.bitmap_geometry
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.suffix_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_inputs
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_ready

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_mapped
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_fresh_seed

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_fresh_global

namespace InitECandidate.Solver.Input.CurrentVerify.FrameOpening
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem parent_names : ofString "ev"∈OriginalScalarGlobals.names ∧ ofString "cur_cont"∈OriginalScalarGlobals.names := by
  decide_cbv

theorem parent_bindings {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage) :
    ∃ parent continuation,source.globals.lookup (ofString "ev")=some (.val (.word parent)) ∧
      source.globals.lookup (ofString "cur_cont")=some (.val (.word continuation)) := by
  obtain ⟨parent,parentCell⟩:=state.environment.arena.scalars _ parent_names.1
  obtain ⟨continuation,continuationCell⟩:=state.environment.arena.scalars _ parent_names.2
  exact ⟨parent,continuation,parentCell,continuationCell⟩

abbrev size : Nat:=104
abbrev recordProgram : ProgHOL 64:=recordCall

def recordFields (parent continuation kind message : BitVec 64) : List FieldStores.Field:=
  [⟨0,.saved "parent" parent⟩,⟨8,.globalSaved "cur_cont" continuation⟩,
   ⟨16,.saved "kind" kind⟩,⟨40,.saved "msg" message⟩]
def activate : ProgHOL 64:=.seq (.assign .global (ofString "ev") (localVar "child"))
  (.seq (.assign .global (ofString "cur_cont") (localVar "rec")) (.return (localVar "child")))

theorem after_clear_shape (parent continuation kind message : BitVec 64) :
    afterClear=FieldStores.program "rec" "unused" (recordFields parent continuation kind message) activate := by
  simp only [afterClear,afterRecord,recordCall,childCall,body,Guest.Software.guestFn_frame_open,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    recordFields,activate,FieldStores.program,FieldStores.address,FieldStores.Value.expression,localVar,addConst]

/-- Actual continuation-record fields, global activation and child return.
These straight-line instructions consume no Pancake evaluator clocks. -/
theorem stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record child parent continuation kind message : BitVec 64)
    (recordLocal : source.locals.lookup (ofString "rec") = some (.val (.word record)))
    (childLocal : source.locals.lookup (ofString "child") = some (.val (.word child)))
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (kindLocal : source.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (mapped : ∀ offset ∈ ([0, 8, 16, 40] : List Nat), source.memaddrs (record + BitVec.ofNat 64 offset)) :
    evaluateHOLFiniteState source afterClear =
      (some (.returned (.val (.word child))), emptyLocalsHOLFinite {source with
        globals := (source.globals.update (ofString "ev", .val (.word child))).update
          (ofString "cur_cont", .val (.word record))
        memory := WitnessRadix.WordWrites.write source.memory (FieldStores.writes record (recordFields parent continuation kind message))}) := by
  have reads : ∀ field ∈ recordFields parent continuation kind message, field.value.Ready source "unused" 0#64 := by
    intro field member
    simp only [recordFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact parentLocal
    · exact continuationGlobal
    · exact kindLocal
    · exact messageLocal
  have fieldsMapped : ∀ field ∈ recordFields parent continuation kind message, source.memaddrs (record + BitVec.ofNat 64 field.offset) := by
    intro field member
    apply mapped
    simp only [recordFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp
  have separate : ∀ reader ∈ recordFields parent continuation kind message, ∀ writer ∈ recordFields parent continuation kind message,
      reader.value.Avoid 0#64 (record + BitVec.ofNat 64 writer.offset) := by
    intro reader member writer _
    simp only [recordFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial
  have fieldsRun := FieldStores.execute source "rec" "unused" record 0#64 (recordFields parent continuation kind message)
    recordLocal reads fieldsMapped separate activate
  let stored := {source with memory := (WitnessRadix.WordWrites.write source.memory (FieldStores.writes record (recordFields parent continuation kind message)))}
  let first := {stored with globals := stored.globals.update (ofString "ev", .val (.word child))}
  let final := {first with globals := first.globals.update (ofString "cur_cont", .val (.word record))}
  have assignChild : evaluateHOLFiniteState stored (.assign .global (ofString "ev") (localVar "child")) = (none, first) := by
    have scalarLocal : stored.locals.lookup (ofString "child") = some (.val (.word child)) := childLocal
    have scalarGlobal : stored.globals.lookup (ofString "ev") = some (.val (.word parent)) := evGlobal
    simp [evaluateHOLFiniteState_assign, localVar, evalHOLExact, toExact, scalarLocal,
      isValidValueHOLExact, lookupKvarHOLExact, scalarGlobal, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite, first]
  have assignRecord : evaluateHOLFiniteState first (.assign .global (ofString "cur_cont") (localVar "rec")) = (none, final) := by
    have scalarLocal : first.locals.lookup (ofString "rec") = some (.val (.word record)) := recordLocal
    have scalarGlobal : first.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)) := by
      simpa [first, HolFiniteMapExact.update, FUPDATE, ofString] using continuationGlobal
    simp [evaluateHOLFiniteState_assign, localVar, evalHOLExact, toExact, scalarLocal,
      isValidValueHOLExact, lookupKvarHOLExact, scalarGlobal, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite, final]
  have returned : evaluateHOLFiniteState final (.return (localVar "child")) = (some (.returned (.val (.word child))), emptyLocalsHOLFinite final) := by
    have scalarLocal : final.locals.lookup (ofString "child") = some (.val (.word child)) := childLocal
    simp [evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, scalarLocal, shapeOfHOLExact]
  have tailRun := WitnessRadix.StateSteps.next_sequence first final
    (.assign .global (ofString "cur_cont") (localVar "rec")) (.return (localVar "child")) assignRecord (Nat.le_refl _)
  rw [returned] at tailRun
  have activeRun := WitnessRadix.StateSteps.next_sequence stored first
    (.assign .global (ofString "ev") (localVar "child"))
    (.seq (.assign .global (ofString "cur_cont") (localVar "rec")) (.return (localVar "child"))) assignChild (Nat.le_refl _)
  rw [tailRun] at activeRun
  change evaluateHOLFiniteState stored activate = (some (.returned (.val (.word child))), emptyLocalsHOLFinite final) at activeRun
  rw [←after_clear_shape parent continuation kind message] at fieldsRun
  rw [activeRun] at fieldsRun
  exact fieldsRun

def recordPointer (scratch : BitVec 64) : BitVec 64 := Arenas.rounded .down scratch 104#64
noncomputable def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  WitnessRadix.QueryBranch.bind (Arenas.post {source with clock := source.clock - 1} .down scratch 104#64) "rec" (recordPointer scratch)
noncomputable def cleared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch : BitVec 64) :=
  {allocated source scratch with
    memory := WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size
    clock := source.clock - 6}
noncomputable def recordFinal (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :=
  let next := cleared source scratch
  {next with
    globals := (next.globals.update (ofString "ev", .val (.word child))).update (ofString "cur_cont", .val (.word (recordPointer scratch)))
    memory := WitnessRadix.WordWrites.write next.memory
      (FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message))}
noncomputable def recordClosed (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :=
  restore source "rec" (emptyLocalsHOLFinite (recordFinal source scratch child parent continuation kind message))

/-- Real continuation-record allocation,104-byte clear, four stores, global
activation, return and scope. The caller must supply original arena mappings;
allocation guards and all intermediate executions are derived. -/
theorem record_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower child parent continuation kind message : BitVec 64)
    (childLocal : source.locals.lookup (ofString "child") = some (.val (.word child)))
    (parentLocal : source.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (kindLocal : source.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower)))
    (code : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (WitnessRadix.Zero.formals, WitnessRadix.Zero.body, .one))
    (lowerAligned : lower.toNat % 8 = 0) (room : lower.toNat + 104 ≤ scratch.toNat)
    (mapped : ∀ offset, offset + 8 ≤ size → offset % 8 = 0 → source.memaddrs (WitnessRadix.byteAddress (recordPointer scratch) offset))
    (enough : 6 ≤ source.clock) :
    evaluateHOLFiniteState source recordProgram =
      (some (.returned (.val (.word child))), recordClosed source scratch child parent continuation kind message) := by
  let entered := allocated source scratch
  let ready := cleared source scratch
  have geometry := Arenas.downward_guards scratch lower 104#64 lowerAligned room
  have recordLocal : entered.locals.lookup (ofString "rec") = some (.val (.word (recordPointer scratch))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address))
      [localVar "rec", .const 104#64] = some (WitnessRadix.Zero.values (recordPointer scratch) size) := by
    simp [evalListHOLFinite, evalListHOLExact, localVar, evalHOLExact, toExact, recordLocal,
      WitnessRadix.Zero.values, size]
  have clearRun := WitnessRadix.Zero.call_execute entered [localVar "rec", .const 104#64] (recordPointer scratch) size
    args zeroCode (by decide) (by decide) geometry.2.2.2.2.2 mapped
    (by change 5 ≤ source.clock - 1; omega)
  have clocks : source.clock - 1 - (WitnessRadix.Zero.price size + 1) = source.clock - 6 := by simp [size, WitnessRadix.Zero.price]; omega
  change evaluateHOLFiniteState entered clear = (none, {entered with
    memory := WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size
    clock := source.clock - 1 - (WitnessRadix.Zero.price size + 1)}) at clearRun
  rw [clocks] at clearRun
  change evaluateHOLFiniteState entered clear = (none, ready) at clearRun
  have readyChild : ready.locals.lookup (ofString "child") = some (.val (.word child)) :=
    (bind_lookup_other _ "rec" "child" _ (by decide)).trans childLocal
  have readyParent : ready.locals.lookup (ofString "parent") = some (.val (.word parent)) :=
    (bind_lookup_other _ "rec" "parent" _ (by decide)).trans parentLocal
  have readyKind : ready.locals.lookup (ofString "kind") = some (.val (.word kind)) :=
    (bind_lookup_other _ "rec" "kind" _ (by decide)).trans kindLocal
  have readyMessage : ready.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "rec" "msg" _ (by decide)).trans messageLocal
  have readyEv : ready.globals.lookup (ofString "ev") = some (.val (.word parent)) := by
    simpa [ready, cleared, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using evGlobal
  have readyCont : ready.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)) := by
    simpa [ready, cleared, allocated, Arenas.post, Arenas.pointerName, WitnessRadix.QueryBranch.bind,
      setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using continuationGlobal
  have storesRun := stores_execute ready (recordPointer scratch) child parent continuation kind message recordLocal readyChild
    readyParent readyKind readyMessage readyEv readyCont (by
      intro offset member
      apply mapped
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide)
  change evaluateHOLFiniteState ready afterClear =
    (some (.returned (.val (.word child))), emptyLocalsHOLFinite (recordFinal source scratch child parent continuation kind message)) at storesRun
  have suffix := WitnessRadix.StateSteps.next_sequence entered ready clear afterClear clearRun
    (by change source.clock - 6 ≤ source.clock - 1; omega)
  rw [storesRun] at suffix
  have allocationRun := Arenas.call_execute source .down "rec" [.const 104#64] (.seq clear afterClear) scratch lower 104#64
    rfl code scratchGlobal lowerGlobal lowerAligned room (by omega)
  change evaluateHOLFiniteState source (.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 104#64] (.seq clear afterClear))=
    (let output:=evaluateHOLFiniteState entered (.seq clear afterClear); (output.1,restore source "rec" output.2)) at allocationRun
  rw [suffix] at allocationRun
  rw [←shapes.2.2.2,←shapes.2.2.1] at allocationRun
  exact allocationRun


/-- Both sides of the continuation allocation are unchanged, including the
child, earlier scratch allocations and persistent memory. -/
theorem record_memory_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower child parent continuation kind message query : BitVec 64)
    (lowerAligned : lower.toNat % 8 = 0) (room : lower.toNat + 104 ≤ scratch.toNat)
    (outside : Arenas.Outside lower scratch query) :
    (recordClosed source scratch child parent continuation kind message).memory query = source.memory query := by
  have geometry := Arenas.downward_guards scratch lower 104#64 lowerAligned room
  have startBound : lower.toNat ≤ (recordPointer scratch).toNat := geometry.2.2.1
  have endBound : (recordPointer scratch).toNat + 104 ≤ scratch.toNat := geometry.2.2.2.1
  have away (offset : Nat) (inside : offset < size) : query ≠ WitnessRadix.byteAddress (recordPointer scratch) offset := by
    change offset < 104 at inside
    have number := WitnessRadix.byteAddress_toNat (recordPointer scratch) offset (by have bound := scratch.isLt; omega)
    intro same
    have equal := congrArg BitVec.toNat same
    rw [number] at equal
    rcases outside with below | high <;> omega
  change WitnessRadix.WordWrites.write (WitnessRadix.Zero.finalMemory source.memory (recordPointer scratch) size)
    (FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message)) query = source.memory query
  rw [WitnessRadix.WordWrites.write_away]
  · exact WitnessRadix.Zero.final_memory_away source.memory (recordPointer scratch) query size away
  · simp only [FieldStores.writes, recordFields, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨away 0 (by decide), away 8 (by decide), away 16 (by decide), away 40 (by decide)⟩


theorem record_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :
    (recordClosed source scratch child parent continuation kind message).clock=source.clock-6 := rfl

theorem record_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :
    (recordClosed source scratch child parent continuation kind message).globals=
      ((source.globals.update (ofString "scratch_ptr",.val (.word (recordPointer scratch)))).update
        (ofString "ev",.val (.word child))).update (ofString "cur_cont",.val (.word (recordPointer scratch))) := rfl

theorem record_words (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :
    (recordClosed source scratch child parent continuation kind message).memory (recordPointer scratch+0#64)=.word parent ∧
    (recordClosed source scratch child parent continuation kind message).memory (recordPointer scratch+8#64)=.word continuation ∧
    (recordClosed source scratch child parent continuation kind message).memory (recordPointer scratch+16#64)=.word kind ∧
    (recordClosed source scratch child parent continuation kind message).memory (recordPointer scratch+40#64)=.word message := by
  have distinct : ((FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message)).map Prod.fst).Nodup := by
    simp [FieldStores.writes,recordFields,BitVec.add_right_inj]
  have field (entry : BitVec 64×BitVec 64) (member : entry∈FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message)) :
      (recordClosed source scratch child parent continuation kind message).memory entry.1=.word entry.2 :=
    WordWrites.write_unique _ _ entry distinct member
  exact ⟨field (recordPointer scratch+0#64,parent) (by simp [FieldStores.writes,recordFields,FieldStores.Value.word]),
    field (recordPointer scratch+8#64,continuation) (by simp [FieldStores.writes,recordFields,FieldStores.Value.word]),
    field (recordPointer scratch+16#64,kind) (by simp [FieldStores.writes,recordFields,FieldStores.Value.word]),
    field (recordPointer scratch+40#64,message) (by simp [FieldStores.writes,recordFields,FieldStores.Value.word])⟩

/-- Every record word not explicitly set by the four metadata stores is
zero from the actual clear, including the continuation state/return fields. -/
theorem record_zero_words (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch child parent continuation kind message : BitVec 64) :
    ∀ offset∈([24,32,48,56,64,72,80,88,96] : List Nat),
      (recordClosed source scratch child parent continuation kind message).memory (recordPointer scratch+BitVec.ofNat 64 offset)=.word 0#64 := by
  intro offset member
  have inside : offset+8≤104 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have aligned : offset%8=0 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  change WordWrites.write (Zero.finalMemory source.memory (recordPointer scratch) 104)
    (FieldStores.writes (recordPointer scratch) (recordFields parent continuation kind message)) (recordPointer scratch+BitVec.ofNat 64 offset)=.word 0#64
  rw [WordWrites.write_away]
  · have number : 8*(offset/8)=offset:=by omega
    simpa only [number] using MutableTable.ZeroWords.final_cell source.memory (recordPointer scratch) 104 (offset/8) (by omega)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [FieldStores.writes,recordFields,BitVec.add_right_inj]

/-- Physical result of the actual first opening. Its origin execution is
retained, and its post-state uses the real dynamic cursors and active record. -/
structure Activated (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (message kind parent continuation record : BitVec 64) (bytes spent : Nat) : Prop where
  bytesBound : bytes≤65536
  spentBound : spent≤bytes
  parentCell : source.globals.lookup (ofString "ev")=some (.val (.word parent))
  continuationCell : source.globals.lookup (ofString "cur_cont")=some (.val (.word continuation))
  actual : evaluateHOLFiniteState source body=(some (.returned (.val (.word FrameConstruction.frameStart))),post)
  clock : post.clock=source.clock-(Zero.price (JumpDest.bitmapBytes bytes)+37+spent)
  recordArena : AllocatedBytes.Arena record 104
  recordAligned : record.toNat%8=0
  recordLower : FrameConstruction.memoryNext.toNat≤record.toNat
  recordAbove : record.toNat+104≤FrameConstruction.frameStart.toNat
  activeFrame : post.globals.lookup (ofString "ev")=some (.val (.word FrameConstruction.frameStart))
  activeRecord : post.globals.lookup (ofString "cur_cont")=some (.val (.word record))
  scratch : post.globals.lookup (ofString "scratch_ptr")=some (.val (.word record))
  frameMemory : post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word FrameConstruction.memoryNext))
  fields : post.memory (record+0#64)=.word parent ∧ post.memory (record+8#64)=.word continuation ∧
    post.memory (record+16#64)=.word kind ∧ post.memory (record+40#64)=.word message
  zeros : ∀ offset∈([24,32,48,56,64,72,80,88,96] : List Nat),post.memory (record+BitVec.ofNat 64 offset)=.word 0#64
  gas : GasBudget.regularBudget post.memory FrameConstruction.frameStart=30000000
  seed : post.memory (FrameConstruction.frameStart+64#64)=.word 30000000#64 ∧
    post.memory (FrameConstruction.frameStart+184#64)=.word 0#64 ∧ post.memory (FrameConstruction.frameStart+192#64)=.word 0#64 ∧
    post.memory (FrameConstruction.frameStart+72#64)=.word 1566720#64
  links : post.memory (FrameConstruction.frameStart+104#64)=.word 1#64 ∧
    post.memory (FrameConstruction.frameStart+112#64)=.word message
  code : post.memory (FrameConstruction.frameStart+48#64)=source.memory (message+112#64) ∧
    post.memory (FrameConstruction.frameStart+56#64)=source.memory (message+120#64)
  globals : ∀ key,key≠ofString "scratch_ptr" → key≠ofString "frame_mem_ptr" → key≠ofString "ev" → key≠ofString "cur_cont" →
    post.globals.lookup key=source.globals.lookup key
  scalars : OriginalScalarGlobals.Scalars post.globals
  memory : ∀ query,Arenas.Outside FrameConstruction.memoryStart FrameConstruction.scratchStart query → post.memory query=source.memory query

/-- First actual frame_open execution, including the genuine child callee,
record allocation/clear/stores, activation and every lexical return. All
entry words, ownership, room and retained gas data are derived. -/
theorem first_execute {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind : BitVec 64}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (messageCell : source.locals.lookup (ofString "msg")=some (.val (.word message)))
    (kindCell : source.locals.lookup (ofString "kind")=some (.val (.word kind)))
    (enough : bodyPrice≤source.clock) :
    ∃ post parent continuation record bytes spent,Activated source post message kind parent continuation record bytes spent := by
  obtain ⟨parent,continuation,parentCell,continuationCell⟩:=parent_bindings state
  let parentSource:=QueryBranch.bind source "parent" parent
  have parentRead : eval source (.var .global (ofString "ev"))=some (.val (.word parent)) := by
    simp [eval,evalHOLExact,toExact,parentCell]
  have messageParent : parentSource.locals.lookup (ofString "msg")=some (.val (.word message)):=
    (bind_lookup_other source "parent" "msg" parent (by decide)).trans messageCell
  have args : evalListHOLFinite parentSource (h:=fun address=>Classical.propDecidable (parentSource.memaddrs address)) [localVar "msg"]=some [.val (.word message)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,messageParent]
  obtain ⟨callee,called,calleeCell⟩:=word_environment parentSource.code.lookup (ofString "frame_new") (ofString "msg") FrameConstruction.body .one message
    (FrameConstruction.original_code source.code state.environment.arena.code)
  let entry:=callEntryStateHOLFinite parentSource callee
  have physical : MessageExecution.Memory entry bs te message target input length accounts storage:=state.of_erase rfl
  obtain ⟨bytes,spent,childPost,bytesBound,spentBound,frameRun,frameClock,frameGas,frameSeed,frameLower,
    ⟨cursor,cursorCell,cursorAligned,cursorNumber,cursorLower⟩,frameGlobals,frameScalars,frameLinks,frameCode,frameMemory⟩:=FrameNormal.first_execute physical calleeCell
      (by change 65830≤source.clock-1; unfold bodyPrice at enough; omega)
  change childPost.clock=source.clock-1-(Zero.price (JumpDest.bitmapBytes bytes)+30+spent) at frameClock
  let recordSource:=CallNormal.continuationEntry parentSource childPost "child" (.val (.word FrameConstruction.frameStart))
  have childLocal : recordSource.locals.lookup (ofString "child")=some (.val (.word FrameConstruction.frameStart)):=CallNormal.continuation_lookup_same _ _ _ _
  have parentLocal : recordSource.locals.lookup (ofString "parent")=some (.val (.word parent)):=
    (CallNormal.continuation_lookup_other parentSource childPost "child" "parent" _ (by decide)).trans (bind_lookup_same source "parent" parent)
  have messageLocal : recordSource.locals.lookup (ofString "msg")=some (.val (.word message)):=
    (CallNormal.continuation_lookup_other parentSource childPost "child" "msg" _ (by decide)).trans messageParent
  have kindLocal : recordSource.locals.lookup (ofString "kind")=some (.val (.word kind)):=
    (CallNormal.continuation_lookup_other parentSource childPost "child" "kind" _ (by decide)).trans
      ((bind_lookup_other source "parent" "kind" parent (by decide)).trans kindCell)
  have evGlobal : recordSource.globals.lookup (ofString "ev")=some (.val (.word parent)):=
    (frameGlobals _ (by decide) (by decide)).trans parentCell
  have contGlobal : recordSource.globals.lookup (ofString "cur_cont")=some (.val (.word continuation)):=
    (frameGlobals _ (by decide) (by decide)).trans continuationCell
  have codeEq : recordSource.code=source.code:=(evaluation_fields entry childPost FrameConstruction.body _ frameRun).2.2.2
  have domain : recordSource.memaddrs=InitE.ordinaryDomain:=
    (evaluation_fields entry childPost FrameConstruction.body _ frameRun).1.trans state.environment.arena.domain
  have installed : OriginalCode.Installed recordSource.code:=by rw [codeEq]; exact state.environment.arena.code
  have bitmapBound:=FrameConstruction.bitmap_bound bytesBound
  have room : FrameConstruction.memoryNext.toNat+104≤cursor.toNat := by
    change 2952791040+104≤cursor.toNat
    omega
  have above : cursor.toNat≤FrameConstruction.frameStart.toNat := by
    change cursor.toNat≤2965298920
    omega
  have geometry:=Arenas.downward_guards cursor FrameConstruction.memoryNext 104#64 (by decide) room
  have recordArena : AllocatedBytes.Arena (recordPointer cursor) 104 := by
    have first:=geometry.2.2.1
    have last:=geometry.2.2.2.1
    change 2952791040≤(recordPointer cursor).toNat at first
    change (recordPointer cursor).toNat+104≤cursor.toNat at last
    constructor
    · omega
    · change cursor.toNat≤2965298920 at above
      omega
  have mapped : ∀ offset,offset+8≤size → offset%8=0 → recordSource.memaddrs (byteAddress (recordPointer cursor) offset) := by
    intro offset inside aligned
    exact AllocatedBytes.word_mapped recordSource (recordPointer cursor) 104 offset domain recordArena
      (by change offset+8≤104 at inside; omega) geometry.2.2.2.2.2 aligned
  have zeroBound : Zero.price (JumpDest.bitmapBytes bytes)≤259 := by
    unfold Zero.price
    omega
  have recordEnough : 6≤recordSource.clock := by
    change 6≤childPost.clock
    unfold bodyPrice at enough
    omega
  have recordRun:=record_execute recordSource cursor FrameConstruction.memoryNext FrameConstruction.frameStart parent continuation kind message
    childLocal parentLocal kindLocal messageLocal evGlobal contGlobal cursorCell frameLower
    (Arenas.original_code recordSource.code installed .down) (Zero.original_code recordSource.code installed)
    (by decide) room mapped recordEnough
  have childRun:=CallNormal.return_execute parentSource childPost "child" .one (ofString "frame_new") [localVar "msg"] [.val (.word message)]
    FrameConstruction.body recordCall callee .one (.val (.word FrameConstruction.frameStart)) args called (by change 1≤source.clock; unfold bodyPrice at enough; omega)
    frameRun (by simp [shapeOfHOLExact,shapeEqHOL])
  change evaluateHOLFiniteState parentSource (.decCall (ofString "child") .one (ofString "frame_new") [localVar "msg"] recordCall)=
    (let output:=evaluateHOLFiniteState recordSource recordProgram; (output.1,restore parentSource "child" output.2)) at childRun
  rw [recordRun,←shapes.2.1] at childRun
  let recordPost:=recordClosed recordSource cursor FrameConstruction.frameStart parent continuation kind message
  let post:=restore source "parent" (restore parentSource "child" recordPost)
  have parentRun:=ScalarScope.declare_execute source _ "parent" (.var .global (ofString "ev")) parent childCall
    (some (.returned (.val (.word FrameConstruction.frameStart)))) parentRead childRun
  rw [←shapes.1] at parentRun
  have actual : evaluateHOLFiniteState source body=(some (.returned (.val (.word FrameConstruction.frameStart))),post):=parentRun
  have records:=record_words recordSource cursor FrameConstruction.frameStart parent continuation kind message
  have zeros:=record_zero_words recordSource cursor FrameConstruction.frameStart parent continuation kind message
  have kept (offset : Nat) (inside : offset<280) :
      post.memory (FrameConstruction.frameStart+BitVec.ofNat 64 offset)=childPost.memory (FrameConstruction.frameStart+BitVec.ofNat 64 offset) := by
    apply record_memory_outside recordSource cursor FrameConstruction.memoryNext FrameConstruction.frameStart parent continuation kind message _ (by decide) room
    apply Or.inr
    have number : (FrameConstruction.frameStart+BitVec.ofNat 64 offset).toNat=2965298920+offset:=
      byteAddress_toNat FrameConstruction.frameStart offset (by change 2965298920+offset<2^64; omega)
    rw [number]
    change cursor.toNat≤2965298920 at above
    omega
  have gas : GasBudget.regularBudget post.memory FrameConstruction.frameStart=30000000 := by
    have same : GasBudget.regularBudget post.memory FrameConstruction.frameStart=GasBudget.regularBudget childPost.memory FrameConstruction.frameStart := by
      simp only [GasBudget.regularBudget,GasBudget.wordAt,kept 64 (by simp),kept 184 (by simp),kept 192 (by simp)]
    exact same.trans frameGas
  refine ⟨post,parent,continuation,recordPointer cursor,bytes,spent,{
    bytesBound:=bytesBound,spentBound:=spentBound,parentCell:=parentCell,continuationCell:=continuationCell,actual:=actual,
    clock:=?_,recordArena:=recordArena,recordAligned:=geometry.2.2.2.2.2,recordLower:=geometry.2.2.1,recordAbove:=?_,
    activeFrame:=?_,activeRecord:=?_,scratch:=?_,frameMemory:=?_,fields:=records,zeros:=zeros,gas:=gas,
    seed:=⟨(kept 64 (by simp)).trans frameSeed.1,(kept 184 (by simp)).trans frameSeed.2.1,
      (kept 192 (by simp)).trans frameSeed.2.2.1,(kept 72 (by simp)).trans frameSeed.2.2.2⟩,
    links:=⟨(kept 104 (by decide)).trans frameLinks.1,(kept 112 (by decide)).trans frameLinks.2⟩,
    code:=⟨(kept 48 (by decide)).trans frameCode.1,(kept 56 (by decide)).trans frameCode.2⟩,
    globals:=?_,scalars:=state.environment.arena.scalars.after actual,memory:=?_}⟩
  · change recordPost.clock=source.clock-_
    rw [record_clock]
    change childPost.clock-6=source.clock-_
    rw [frameClock]
    omega
  · have finish:=geometry.2.2.2.1
    change (recordPointer cursor).toNat+104≤cursor.toNat at finish
    omega
  · change recordPost.globals.lookup (ofString "ev")=_
    rw [record_globals]
    simp [HolFiniteMapExact.update,FUPDATE,ofString]
  · change recordPost.globals.lookup (ofString "cur_cont")=_
    rw [record_globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  · change recordPost.globals.lookup (ofString "scratch_ptr")=_
    rw [record_globals]
    simp [HolFiniteMapExact.update,FUPDATE,ofString]
  · change recordPost.globals.lookup (ofString "frame_mem_ptr")=_
    rw [record_globals]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString] using
      (show recordSource.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word FrameConstruction.memoryNext)) from frameLower)
  · intro key notScratch notFrame notEv notCont
    change recordPost.globals.lookup key=source.globals.lookup key
    rw [record_globals]
    have retained : recordSource.globals.lookup key=source.globals.lookup key:=frameGlobals key notScratch notFrame
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm notScratch,Ne.symm notEv,Ne.symm notCont] using retained
  · intro query outside
    have recordOutside : Arenas.Outside FrameConstruction.memoryNext cursor query := by
      rcases outside with before|after
      · apply Or.inl
        change query.toNat<2952790016 at before
        change query.toNat<2952791040
        omega
      · apply Or.inr
        change 2965299200≤query.toNat at after
        change cursor.toNat≤2965298920 at above
        omega
    exact (record_memory_outside recordSource cursor FrameConstruction.memoryNext FrameConstruction.frameStart parent continuation kind message query
      (by decide) room recordOutside).trans (frameMemory query outside)

/-- The whole activated frame/record operation preserves the actual
message record, including the newly derived flags; this uses the real
message/table ordering rather than startup-cursor equality at the post-state. -/
theorem Activated.message_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind parent previous record : BitVec 64} {bytes spent : Nat}
    (activated : Activated source post message kind parent previous record bytes spent)
    (entry : MessageExecution.Memory source bs te message target input length accounts storage) :
    ∀ offset : Nat,offset<176 → post.memory (message+BitVec.ofNat 64 offset)=source.memory (message+BitVec.ofNat 64 offset) := by
  obtain ⟨first,second,third⟩:=FrameConstruction.memory_layout entry
  have before : message.toNat+176≤2952790016:=by omega
  intro offset inside
  apply activated.memory
  apply Or.inl
  have number : (message+BitVec.ofNat 64 offset).toNat=message.toNat+offset:=byteAddress_toNat message offset (by omega)
  rw [number]
  change message.toNat+offset<2952790016
  omega

theorem Activated.message_flags {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind parent previous record : BitVec 64} {bytes spent : Nat}
    (activated : Activated source post message kind parent previous record bytes spent)
    (entry : MessageExecution.Memory source bs te message target input length accounts storage) :
    UncheckedSystem.MessageFlags post message:=entry.flags.of_record_memory (activated.message_memory entry)

theorem Activated.message_words {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind parent previous record : BitVec 64} {bytes spent : Nat}
    (activated : Activated source post message kind parent previous record bytes spent)
    (entry : MessageExecution.Memory source bs te message target input length accounts storage) :
    UncheckedSystem.MessageWords post te message target input length:=
  entry.words.of_memory (fun offset inside=>activated.message_memory entry offset (by omega))

/-- The real caller either has already spent at most its opening allowance,
or reaches its unchanged continuation with a genuinely activated frame.
The receipt retains the actual two-word ABI and its callee entry model. -/
theorem call_trace {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind : BitVec 64}
    (state : MessageExecution.Entry source bs te message target input length accounts storage)
    (name : String) (arguments : List (ExpHOL 64)) (continuationProgram : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values message kind))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "frame_open") arguments continuationProgram)=(outcome,post)) :
    source.clock-post.clock≤bodyPrice+1 ∨
      ∃ callee opened current inner parent previous record bytes spent,
        lookupCodeHOLFinite source.code.lookup (ofString "frame_open") (values message kind)=some (body,callee,.one) ∧
        MessageExecution.Entry (callEntryStateHOLFinite source callee) bs te message target input length accounts storage ∧
        Activated (callEntryStateHOLFinite source callee) opened message kind parent previous record bytes spent ∧
        current=CallNormal.continuationEntry source opened name (.val (.word FrameConstruction.frameStart)) ∧
        current.locals.lookup (ofString name)=some (.val (.word FrameConstruction.frameStart)) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤bodyPrice+1 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current continuationProgram=(outcome,inner) := by
  by_cases short : source.clock≤bodyPrice+1
  · exact Or.inl (by omega)
  · obtain ⟨callee,called,entry,kindCell⟩:=call_environment state kind
    obtain ⟨opened,parent,previous,record,bytes,spent,activated⟩:=first_execute entry.memory entry.cell kindCell
      (by change 65967≤source.clock-1; unfold bodyPrice at short; omega)
    let current:=CallNormal.continuationEntry source opened name (.val (.word FrameConstruction.frameStart))
    let inner:=(evaluateHOLFiniteState current continuationProgram).2
    have replay:=CallNormal.return_execute source opened name .one (ofString "frame_open") arguments (values message kind)
      body continuationProgram callee .one (.val (.word FrameConstruction.frameStart)) args called
      (by unfold bodyPrice at short; omega) activated.actual (by simp [shapeOfHOLExact,shapeEqHOL])
    rw [replay] at run
    have resultEq:=congrArg Prod.fst run
    have endpoint : post=restore source name inner:=(congrArg Prod.snd run).symm
    have continued : evaluateHOLFiniteState current continuationProgram=(outcome,inner):=Prod.ext resultEq rfl
    have bodyCost:=body_cost entry.memory entry.cell
    rw [activated.actual] at bodyCost
    change source.clock-1-opened.clock≤bodyPrice at bodyCost
    have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    rw [activated.actual] at forward
    change opened.clock≤source.clock-1 at forward
    refine Or.inr ⟨callee,opened,current,inner,parent,previous,record,bytes,spent,called,entry,activated,rfl,
      CallNormal.continuation_lookup_same source opened name _,?_,?_,?_,continued⟩
    · change opened.clock≤source.clock; omega
    · change source.clock-opened.clock≤bodyPrice+1; omega
    · rw [endpoint]; exact ⟨rfl,rfl⟩

end InitECandidate.Solver.Input.CurrentVerify.FrameOpening

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.parent_names
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.parent_bindings
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.after_clear_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.stores_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_memory_outside

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_clock
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_words

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.record_zero_words

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.first_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.call_trace

namespace InitECandidate.Solver.Input.CurrentVerify.ProcessMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real process_message prefix and opening, including the normal depth
guard and actual parent declarations. A reached state carries its genuine
activated-record receipt and exact original afterOpen continuation. -/
theorem body_to_opened {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage : BitVec 64}
    (state : Entry source bs te message target input length accounts storage)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤65968 ∨
      ∃ caller callee opened current inner parent previous record bytes spent,
        CallPrefix.Execution source prefixActions caller ∧ Entry caller bs te message target input length accounts storage ∧
        (∃ depth,caller.memory (message+128#64)=.word depth ∧ depth.toNat≤1024) ∧
        lookupCodeHOLFinite caller.code.lookup (ofString "frame_open") (FrameOpening.values message 0#64)=some (FrameOpening.body,callee,.one) ∧
        Entry (callEntryStateHOLFinite caller callee) bs te message target input length accounts storage ∧
        FrameOpening.Activated (callEntryStateHOLFinite caller callee) opened message 0#64 parent previous record bytes spent ∧
        current=CallNormal.continuationEntry caller opened "child" (.val (.word FrameConstruction.frameStart)) ∧
        current.locals.lookup (ofString "child")=some (.val (.word FrameConstruction.frameStart)) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤65968 ∧ CallPrefix.ScopeFrame post inner ∧
        evaluateHOLFiniteState current afterOpen=(outcome,inner) := by
  rw [prefix_shapes.1] at run
  rcases CallPrefix.priced_frame_trace source post prefixActions openCall 0 (prefix_cost source.code source rfl) outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,outer,execution,forward,price,scope,continued⟩:=reached
    obtain ⟨entry,depth⟩:=prefix_facts state execution
    have args : evalListHOLFinite caller (h:=fun address=>Classical.propDecidable (caller.memaddrs address)) [localVar "msg",.const 0#64]=
        some (FrameOpening.values message 0#64) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,entry.cell,FrameOpening.values]
    rw [prefix_shapes.2] at continued
    rcases FrameOpening.call_trace entry "child" [localVar "msg",.const 0#64] afterOpen args outcome continued with stopped|opened
    · have clock:=scope.clock
      unfold FrameOpening.bodyPrice at stopped
      exact Or.inl (by omega)
    · obtain ⟨callee,openedState,current,inner,parent,previous,record,bytes,spent,called,calleeEntry,activated,resumed,childCell,
        currentForward,currentPrice,currentScope,rest⟩:=opened
      unfold FrameOpening.bodyPrice at currentPrice
      exact Or.inr ⟨caller,callee,openedState,current,inner,parent,previous,record,bytes,spent,execution,entry,depth,called,calleeEntry,activated,
        resumed,childCell,by omega,by omega,scope.trans currentScope,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.ProcessMessage

#print axioms InitECandidate.Solver.Input.CurrentVerify.ProcessMessage.body_to_opened

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.Activated.message_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.Activated.message_flags
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.Activated.message_words

namespace InitECandidate.Solver.Input.CurrentVerify.JournalSnapshot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64:=match Guest.Software.guestFn_state_snapshot with | .function fn=>progToHOL fn.body | _=>.skip

theorem shape : body=.return (.var .global (ofString "journal_n")) := by
  simp only [body,Guest.Software.guestFn_state_snapshot,progToHOL,expToHOL]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "state_snapshot")=some ([],body,.one) := by
  have checked:=OriginalCode.indexed code installed 324
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_state_snapshot) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_state_snapshot,shapeToHOL,List.map_nil] using checked

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem counter_name : ofString "journal_n" ∈ OriginalScalarGlobals.names := by decide_cbv

/-- A real snapshot reads the declared scalar counter and changes no memory
or global. Its caller pays exactly one source tick; no rollback image or
future helper outcome is an input to this receipt. -/
theorem call_reaches (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (name : String) (funded : 1≤source.clock) :
    ∃ count : BitVec 64,source.globals.lookup (ofString "journal_n")=some (.val (.word count)) ∧
      CallPrefix.Reaches source (.scoped (ofString name) .one (ofString "state_snapshot") [])
        (QueryBranch.bind {source with clock:=source.clock-1} name count) := by
  obtain ⟨count,counter⟩:=scalars (ofString "journal_n") counter_name
  have raw : lookupCodeHOLExact source.code.lookup (ofString "state_snapshot") []=some (body,(fun _=>none),.one) := by
    simp [lookupCodeHOLExact,original_code source.code installed]
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup (ofString "state_snapshot") [] body (fun _=>none) .one raw
  let entry:=callEntryStateHOLFinite source callee
  have entryCounter : entry.globals.lookup (ofString "journal_n")=some (.val (.word count)):=counter
  have run : evaluateHOLFiniteState entry body=(some (.returned (.val (.word count))),emptyLocalsHOLFinite entry) := by
    rw [shape]
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,entryCounter,shapeOfHOLExact]
  refine ⟨count,counter,?_⟩
  exact CallPrefix.Reaches.scoped source (ofString name) .one (ofString "state_snapshot") [] [] body callee .one
    (.val (.word count)) (emptyLocalsHOLFinite entry) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])

end InitECandidate.Solver.Input.CurrentVerify.JournalSnapshot

#print axioms InitECandidate.Solver.Input.CurrentVerify.JournalSnapshot.shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.JournalSnapshot.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.JournalSnapshot.counter_name
#print axioms InitECandidate.Solver.Input.CurrentVerify.JournalSnapshot.call_reaches

namespace InitECandidate.Solver.Input.CurrentVerify.ProcessMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def depthPreparation : ProgHOL 64:=match afterOpen with | .seq _ (.seq (.ite _ yes _) _)=>yes | _=>.skip
def afterPreparation : ProgHOL 64:=match afterOpen with | .seq _ (.seq _ rest)=>rest | _=>.skip
def preparationActions : List CallPrefix.Action:=
  [.scoped (ofString "prep_snapshot") .one (ofString "state_snapshot") [],
   .declare (ofString "prep_reservoir") .one (.load .one (Scalar.plus (localVar "msg") 48)),
   .declare (ofString "perr") .one (.const 0#64)]
def preparationCall : ProgHOL 64:=(CallPrefix.cutAt 3 depthPreparation).2

theorem preparation_shapes :
    afterOpen=.seq .skip (.seq (.ite (.cmp .equal depthExpression (.const 0#64)) depthPreparation .skip) afterPreparation) ∧
    depthPreparation=CallPrefix.program preparationActions preparationCall := by
  simp only [depthPreparation,afterPreparation,afterOpen,openCall,CallPrefix.cutAt,body,
    Guest.Software.guestFn_process_message,progToHOL,expToHOL,shapeToHOL,depthExpression,
    Scalar.plus,localVar,preparationActions,preparationCall,CallPrefix.program,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  trivial

/-- The real zero-depth word selects the original preparation branch.
The domain and physical message record may have dynamic arena cursors. -/
theorem after_open_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (message : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena message 176)
    (aligned : message.toNat%8=0)
    (cell : source.locals.lookup (ofString "msg")=some (.val (.word message)))
    (flags : UncheckedSystem.MessageFlags source message) :
    evaluateHOLFiniteState source afterOpen=evaluateHOLFiniteState source (.seq depthPreparation afterPreparation) := by
  have address:=Scalar.plus_read source (localVar "msg") message 128 (by simp [eval,evalHOLExact,localVar,toExact,cell])
  have read:=Witness.load_word_read source _ (message+128#64) 0#64 address
    (AllocatedBytes.word_mapped source message 176 128 domain arena (by decide) aligned (by decide))
    (flags 128 (by decide))
  change eval source depthExpression=some (.val (.word 0#64)) at read
  have test : eval source (.cmp .equal depthExpression (.const 0#64))=some (.val (.word 1#64)) := by
    simp only [eval] at read
    simp [eval,evalHOLExact,read,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test
  rw [preparation_shapes.1]
  simp only [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_ite,test]
  simp

/-- Every lexical setup action before the actual caught depth0_prepare call
executes from the physical post-opening message facts. The saved snapshot is
the observed journal counter; memory and globals remain exactly unchanged. -/
theorem preparation_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (message : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena message 176)
    (aligned : message.toNat%8=0)
    (cell : source.locals.lookup (ofString "msg")=some (.val (.word message)))
    (reservoir : source.memory (message+48#64)=.word 1566720#64)
    (funded : 1≤source.clock) :
    ∃ count current,source.globals.lookup (ofString "journal_n")=some (.val (.word count)) ∧
      CallPrefix.Execution source preparationActions current ∧
      current.clock=source.clock-1 ∧ LocalEffects.erase current=LocalEffects.erase source ∧
      current.locals.lookup (ofString "msg")=some (.val (.word message)) ∧
      current.locals.lookup (ofString "prep_snapshot")=some (.val (.word count)) ∧
      current.locals.lookup (ofString "prep_reservoir")=some (.val (.word 1566720#64)) ∧
      current.locals.lookup (ofString "perr")=some (.val (.word 0#64)) := by
  obtain ⟨count,counter,snapshot⟩:=JournalSnapshot.call_reaches source installed scalars "prep_snapshot" funded
  let snap:=QueryBranch.bind {source with clock:=source.clock-1} "prep_snapshot" count
  let saved:=QueryBranch.bind snap "prep_reservoir" 1566720#64
  let current:=QueryBranch.bind saved "perr" 0#64
  have messageCell : snap.locals.lookup (ofString "msg")=some (.val (.word message)):=
    (bind_lookup_other _ "prep_snapshot" "msg" count (by decide)).trans cell
  have address:=Scalar.plus_read snap (localVar "msg") message 48 (by simp [eval,evalHOLExact,localVar,toExact,messageCell])
  have read:=Witness.load_word_read snap _ (message+48#64) 1566720#64 address
    (AllocatedBytes.word_mapped snap message 176 48 domain arena (by decide) aligned (by decide)) reservoir
  refine ⟨count,current,counter,?_,rfl,rfl,?_,?_,?_,?_⟩
  · exact .step snapshot (.step (.declare snap (ofString "prep_reservoir") .one _ (.val (.word 1566720#64)) read (by simp [shapeOfHOLExact,shapeEqHOL]))
      (.step (.declare saved (ofString "perr") .one (.const 0#64) (.val (.word 0#64)) rfl (by simp [shapeOfHOLExact,shapeEqHOL])) (.done current)))
  · simpa [current,saved,snap,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using cell
  · simp [current,saved,snap,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  · simp [current,saved,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
  · exact bind_lookup_same saved "perr" 0#64

end InitECandidate.Solver.Input.CurrentVerify.ProcessMessage

#print axioms InitECandidate.Solver.Input.CurrentVerify.ProcessMessage.preparation_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.ProcessMessage.after_open_selected
#print axioms InitECandidate.Solver.Input.CurrentVerify.ProcessMessage.preparation_prefix

namespace InitECandidate.Solver.Input.CurrentVerify.ProcessMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The genuine frame-opening receipt supplies every preparation condition
at the restored process_message caller. No fixed startup cursors, zero-depth
premise, saved snapshot or future depth0_prepare result is assumed. -/
theorem opened_preparation {caller opened : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage parent previous record : BitVec 64} {bytes spent : Nat}
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (state : Entry caller bs te message target input length accounts storage)
    (activated : FrameOpening.Activated (callEntryStateHOLFinite caller callee) opened message 0#64 parent previous record bytes spent)
    (funded : 1≤opened.clock) :
    let resumed:=CallNormal.continuationEntry caller opened "child" (.val (.word FrameConstruction.frameStart))
    ∃ count current,
      evaluateHOLFiniteState resumed afterOpen=evaluateHOLFiniteState resumed (.seq depthPreparation afterPreparation) ∧
      resumed.globals.lookup (ofString "journal_n")=some (.val (.word count)) ∧
      CallPrefix.Execution resumed preparationActions current ∧
      CallPrefix.observe (evaluateHOLFiniteState resumed depthPreparation)=CallPrefix.observe (evaluateHOLFiniteState current preparationCall) ∧
      current.clock=opened.clock-1 ∧ LocalEffects.erase current=LocalEffects.erase opened ∧
      current.locals.lookup (ofString "child")=some (.val (.word FrameConstruction.frameStart)) ∧
      current.locals.lookup (ofString "msg")=some (.val (.word message)) ∧
      current.locals.lookup (ofString "prep_snapshot")=some (.val (.word count)) ∧
      current.locals.lookup (ofString "prep_reservoir")=some (.val (.word 1566720#64)) ∧
      current.locals.lookup (ofString "perr")=some (.val (.word 0#64)) := by
  let resumed:=CallNormal.continuationEntry caller opened "child" (.val (.word FrameConstruction.frameStart))
  have physical : MessageExecution.Memory (callEntryStateHOLFinite caller callee) bs te message target input length accounts storage:=
    state.memory.of_erase rfl
  have fields:=evaluation_fields (callEntryStateHOLFinite caller callee) opened FrameOpening.body
    (some (.returned (.val (.word FrameConstruction.frameStart)))) activated.actual
  have domain : resumed.memaddrs=InitE.ordinaryDomain:=fields.1.trans state.memory.environment.arena.domain
  have openedInstalled : OriginalCode.Installed opened.code:=
    OriginalCode.after_execution (callEntryStateHOLFinite caller callee) opened FrameOpening.body
      (some (.returned (.val (.word FrameConstruction.frameStart)))) activated.actual state.memory.environment.arena.code
  have installed : OriginalCode.Installed resumed.code:=openedInstalled
  have scalars : OriginalScalarGlobals.Scalars resumed.globals:=activated.scalars
  have cell : resumed.locals.lookup (ofString "msg")=some (.val (.word message)):=
    (CallNormal.continuation_lookup_other caller opened "child" "msg" _ (by decide)).trans state.cell
  have flags : UncheckedSystem.MessageFlags resumed message:=activated.message_flags physical
  have words : UncheckedSystem.MessageWords resumed te message target input length:=
    (activated.message_words physical).of_memory (by intro offset inside; rfl)
  have selected:=after_open_selected resumed message domain state.memory.messageArena state.memory.messageAligned cell flags
  obtain ⟨count,current,counter,execution,clock,metadata,messageCell,snapshotCell,reservoirCell,errorCell⟩:=
    preparation_prefix resumed message installed scalars domain state.memory.messageArena state.memory.messageAligned cell words.stateGas funded
  have observed:=execution.observe preparationCall
  rw [←preparation_shapes.2] at observed
  refine ⟨count,current,selected,counter,execution,observed,clock,metadata,?_,messageCell,snapshotCell,reservoirCell,errorCell⟩
  rw [execution.keeps_local (ofString "child") ?_]
  · exact CallNormal.continuation_lookup_same caller opened "child" _
  · intro action member
    simp only [preparationActions,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact CallPrefix.KeepsLocal.scoped _ _ _ _ _ (by decide)
    · exact CallPrefix.KeepsLocal.declared _ _ _ _ (by decide)
    · exact CallPrefix.KeepsLocal.declared _ _ _ _ (by decide)

end InitECandidate.Solver.Input.CurrentVerify.ProcessMessage

#print axioms InitECandidate.Solver.Input.CurrentVerify.ProcessMessage.opened_preparation

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.DeleteSafe.of_suffix
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.delete_safe_outside
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.delete_link_safe
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameNormal.first_fresh_code

namespace InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64:=match Guest.Software.guestFn_depth0_prepare with | .function fn=>progToHOL fn.body | _=>.skip

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "depth0_prepare")=some ([],body,.one) := by
  have checked:=OriginalCode.indexed code installed 539
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_depth0_prepare) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_depth0_prepare,shapeToHOL,List.map_nil] using checked

def messageExpression : ExpHOL 64:=.load .one (Scalar.plus (.var .global (ofString "ev")) 112)
def environmentExpression : ExpHOL 64:=.load .one (Scalar.plus (localVar "msg") 8)
def prefixActions : List CallPrefix.Action:=
  [.command .skip,.declare (ofString "msg") .one messageExpression,.declare (ofString "te") .one environmentExpression]
def delegationSite : ProgHOL 64:=(CallPrefix.cutAt 3 body).2

theorem prefix_shape : body=CallPrefix.program prefixActions delegationSite := by
  simp only [body,delegationSite,CallPrefix.cutAt,Guest.Software.guestFn_depth0_prepare,progToHOL,expToHOL,shapeToHOL,
    prefixActions,messageExpression,environmentExpression,Scalar.plus,localVar,CallPrefix.program,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem prefix_cost (code) : ClockCost.Bound code (CallPrefix.program prefixActions .skip) 0 := by
  apply ClockCost.of_quiet
  exact QuietClock.sequence code _ _ (QuietClock.skip code)
    (QuietClock.declared code _ _ _ _ (QuietClock.declared code _ _ _ _ (QuietClock.skip code)))

/-- Actual entry reads in depth0_prepare: ev points at the genuinely opened
frame, whose112slot supplies msg, whose8slot supplies the real TE pointer.
Caller restoration and the pure preparation prefix may change locals/clocks;
their actual nonlocal frame suffices. No delegation value is assumed here. -/
theorem first_prefix {source opened current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage parent previous record : BitVec 64} {bytes spent : Nat}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (activated : FrameOpening.Activated source opened message 0#64 parent previous record bytes spent)
    (same : LocalEffects.erase current=LocalEffects.erase opened) :
    ∃ ready,CallPrefix.Execution current prefixActions ready ∧
      ready.clock=current.clock ∧ LocalEffects.erase ready=LocalEffects.erase opened ∧
      ready.locals.lookup (ofString "msg")=some (.val (.word message)) ∧
      ready.locals.lookup (ofString "te")=some (.val (.word te)) := by
  have memory : current.memory=opened.memory:=LocalEffects.memory_of_erase opened current same
  have globals : current.globals=opened.globals:=by
    have projected:=congrArg PanSemStateFiniteExact.globals same
    exact projected
  have fields:=evaluation_fields source opened FrameOpening.body
    (some (.returned (.val (.word FrameConstruction.frameStart)))) activated.actual
  have domain : current.memaddrs=InitE.ordinaryDomain:=by
    have retained : current.memaddrs=opened.memaddrs:=by
      have projected:=congrArg PanSemStateFiniteExact.memaddrs same
      exact projected
    exact retained.trans (fields.1.trans state.environment.arena.domain)
  have frameCell : current.memory (FrameConstruction.frameStart+112#64)=.word message:=by rw [memory]; exact activated.links.2
  have frameGlobal : current.globals.lookup (ofString "ev")=some (.val (.word FrameConstruction.frameStart)):=by rw [globals]; exact activated.activeFrame
  have address:=Scalar.plus_read current (.var .global (ofString "ev")) FrameConstruction.frameStart 112
    (by simp [eval,evalHOLExact,toExact,frameGlobal])
  have messageRead : eval current messageExpression=some (.val (.word message)):=
    Witness.load_word_read current _ (FrameConstruction.frameStart+112#64) message address
      (AllocatedBytes.word_mapped current FrameConstruction.frameStart 280 112 domain ⟨by decide,by decide⟩ (by decide) (by decide) (by decide)) frameCell
  let messageState:=QueryBranch.bind current "msg" message
  let ready:=QueryBranch.bind messageState "te" te
  have environmentCell : messageState.memory (message+8#64)=.word te:=by
    change current.memory (message+8#64)=.word te
    rw [memory]
    exact (activated.message_words state).environment
  have msgCell : messageState.locals.lookup (ofString "msg")=some (.val (.word message)):=bind_lookup_same current "msg" message
  have environmentAddress:=Scalar.plus_read messageState (localVar "msg") message 8
    (by simp [eval,evalHOLExact,toExact,localVar,msgCell])
  have environmentRead : eval messageState environmentExpression=some (.val (.word te)):=
    Witness.load_word_read messageState _ (message+8#64) te environmentAddress
      (AllocatedBytes.word_mapped messageState message 176 8 domain state.messageArena (by decide) state.messageAligned (by decide)) environmentCell
  refine ⟨ready,?_,rfl,same,?_,bind_lookup_same _ _ _⟩
  · exact .step (.command current current .skip (evaluateHOLFiniteState_skip current))
      (.step (.declare current (ofString "msg") .one messageExpression (.val (.word message)) messageRead (by simp [shapeOfHOLExact,shapeEqHOL]))
      (.step (.declare messageState (ofString "te") .one environmentExpression (.val (.word te)) environmentRead (by simp [shapeOfHOLExact,shapeEqHOL])) (.done ready)))
  · exact (bind_lookup_other messageState "te" "msg" te (by decide)).trans (bind_lookup_same current "msg" message)

end InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation

#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.prefix_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.first_prefix

namespace InitECandidate.Solver.Input.CurrentVerify.FrameOpening
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual entire TE is below the new frame arena. Its cleared
delegation field survives frame construction and record activation. -/
theorem Activated.environment_memory {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind parent previous record : BitVec 64} {bytes spent : Nat}
    (activated : Activated source post message kind parent previous record bytes spent)
    (entry : MessageExecution.Memory source bs te message target input length accounts storage) :
    ∀ offset : Nat,offset<200 → post.memory (te+BitVec.ofNat 64 offset)=source.memory (te+BitVec.ofNat 64 offset) := by
  obtain ⟨first,second,third⟩:=FrameConstruction.memory_layout entry
  have earlier:=entry.afterEnvironment
  have before : te.toNat+200≤2952790016:=by omega
  intro offset inside
  apply activated.memory
  apply Or.inl
  have number : (te+BitVec.ofNat 64 offset).toNat=te.toNat+offset:=byteAddress_toNat te offset (by omega)
  rw [number]
  change te.toNat+offset<2952790016
  omega

theorem Activated.environment_delegations {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage kind parent previous record : BitVec 64} {bytes spent : Nat}
    (activated : Activated source post message kind parent previous record bytes spent)
    (entry : MessageExecution.Memory source bs te message target input length accounts storage) :
    post.memory (te+152#64)=.word 0#64:=
  (activated.environment_memory entry 152 (by decide)).trans entry.delegations

end InitECandidate.Solver.Input.CurrentVerify.FrameOpening

#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.Activated.environment_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.FrameOpening.Activated.environment_delegations

namespace InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def delegationCondition : ExpHOL 64:=.cmp .notEqual (.load .one (Scalar.plus (localVar "te") 152)) (.const 0#64)
def delegationBody : ProgHOL 64:=match delegationSite with | .seq (.ite _ yes _) _=>yes | _=>.skip
def dispatchCall : ProgHOL 64:=.call (some (none,none)) (ofString "prepare_dispatch") []
def afterDispatch : ProgHOL 64:=.seq .skip (.return (.const 0#64))

theorem delegation_shape : delegationSite=.seq (.ite delegationCondition delegationBody .skip)
    (.seq .skip (.seq dispatchCall afterDispatch)) := by
  simp only [delegationSite,CallPrefix.cutAt,body,Guest.Software.guestFn_depth0_prepare,progToHOL,expToHOL,shapeToHOL,
    delegationCondition,delegationBody,Scalar.plus,localVar,dispatchCall,afterDispatch,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]

/-- A genuine mapped zero TE152 selects the no-delegation branch, retaining
the original prepare_dispatch call and its unchanged return continuation. -/
theorem no_delegation_selected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (te : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena te 200)
    (aligned : te.toNat%8=0)
    (cell : source.locals.lookup (ofString "te")=some (.val (.word te)))
    (empty : source.memory (te+152#64)=.word 0#64) :
    evaluateHOLFiniteState source delegationSite=evaluateHOLFiniteState source (.seq dispatchCall afterDispatch) := by
  classical
  have address:=Scalar.plus_read source (localVar "te") te 152 (by simp [eval,evalHOLExact,toExact,localVar,cell])
  have read:=Witness.load_word_read source _ (te+152#64) 0#64 address
    (AllocatedBytes.word_mapped source te 200 152 domain arena (by decide) aligned (by decide)) empty
  have test : eval source delegationCondition=some (.val (.word 0#64)) := by
    simp only [eval] at read
    change evalHOLExact source.toExact delegationCondition=_
    rw [delegationCondition,evalHOLExact,read]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have guard : evaluateHOLFiniteState source (.ite delegationCondition delegationBody .skip)=(none,source) := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite,test]
    simp [evaluateHOLFiniteState_skip]
  rw [delegation_shape,evaluateHOLFiniteState_seq_line780,guard]
  simp only [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip]

/-- From the actual opened system message, the whole depth0_prepare prefix
reads its genuine msg/TE and skips delegation. Its next call is the original
prepare_dispatch, with every nonlocal field retained and no future success
assumption. The actual caller-local reset is allowed by the supplied frame. -/
theorem first_dispatch {source opened current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {bs te message target input length accounts storage parent previous record : BitVec 64} {bytes spent : Nat}
    (state : MessageExecution.Memory source bs te message target input length accounts storage)
    (activated : FrameOpening.Activated source opened message 0#64 parent previous record bytes spent)
    (same : LocalEffects.erase current=LocalEffects.erase opened) :
    ∃ ready,CallPrefix.Execution current prefixActions ready ∧ ready.clock=current.clock ∧
      LocalEffects.erase ready=LocalEffects.erase opened ∧
      ready.locals.lookup (ofString "msg")=some (.val (.word message)) ∧
      ready.locals.lookup (ofString "te")=some (.val (.word te)) ∧
      CallPrefix.observe (evaluateHOLFiniteState current body)=
        CallPrefix.observe (evaluateHOLFiniteState ready (.seq dispatchCall afterDispatch)) := by
  obtain ⟨ready,execution,clock,metadata,messageCell,teCell⟩:=first_prefix state activated same
  have fields:=evaluation_fields source opened FrameOpening.body
    (some (.returned (.val (.word FrameConstruction.frameStart)))) activated.actual
  have domain : ready.memaddrs=InitE.ordinaryDomain:=by
    have retained:=congrArg PanSemStateFiniteExact.memaddrs metadata
    change ready.memaddrs=opened.memaddrs at retained
    exact retained.trans (fields.1.trans state.environment.arena.domain)
  have memory : ready.memory=opened.memory:=LocalEffects.memory_of_erase opened ready metadata
  have empty : ready.memory (te+152#64)=.word 0#64:=by rw [memory]; exact activated.environment_delegations state
  have selected:=no_delegation_selected ready te domain state.environmentArena state.environmentAligned teCell empty
  have observed:=execution.observe delegationSite
  rw [←prefix_shape,selected] at observed
  exact ⟨ready,execution,clock,metadata,messageCell,teCell,observed⟩

end InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation

#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.delegation_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.no_delegation_selected
#print axioms InitECandidate.Solver.Input.CurrentVerify.DepthZeroPreparation.first_dispatch
