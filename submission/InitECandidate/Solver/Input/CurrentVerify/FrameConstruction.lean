import InitECandidate.Solver.Input.CurrentVerify.FreshTransactionMemory
import InitECandidate.Solver.GasBudget.FrameNewFresh
import InitECandidate.Solver.JumpDest.Call
import InitECandidate.Solver.Arenas.Cost

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
      words.length.toNat≤65536 ∧ (words.length=0#64 ∨ AllocatedBytes.Arena words.code words.length.toNat) ∧
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
  refine ⟨words,bound,arena,pointerCell,bytesCell,?_⟩
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
  · obtain ⟨words,bound,codeArena,pointerCell,bytesCell,prefixRun⟩:=actual_prefix state messageCell (by unfold bodyPrice at short; omega)
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
