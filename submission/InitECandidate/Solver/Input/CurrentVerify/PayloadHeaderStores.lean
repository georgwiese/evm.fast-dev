import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
import InitECandidate.Solver.Input.CallPrefixCommand
import InitECandidate.Solver.WitnessRadix.ZeroNormal
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.MutableTable.ZeroWords

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def zeroHeader : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "h",.const 248#64]
def afterClear : List CallPrefix.Action:=afterHeader.drop 1
def afterFirstStores : List CallPrefix.Action:=afterClear.drop 2
def clearedHeader (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  let allocated:=headerEntry source pointer record heap
  {allocated with memory:=Zero.finalMemory allocated.memory heap 248,clock:=allocated.clock-(Zero.price 248+1)}
def putHeader (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (offset : Nat) (word : BitVec 64):=
  {source with memory:=StoreWord.put source.memory (heap+BitVec.ofNat 64 offset) word}
def firstStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  putHeader (putHeader (clearedHeader source pointer record heap) heap 0 1#64) heap 8 (pointer+62#64)
def headerField (offset : Nat) : ExpHOL 64:=.op .add [localVar "h",.const (BitVec.ofNat 64 offset)]

set_option maxRecDepth 100000 in
theorem clearing_action : afterHeader=.command zeroHeader::afterClear := by
  simp only [afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterClear,zeroHeader,localVar]
  rfl

set_option maxRecDepth 100000 in
theorem first_store_actions : afterClear=.command (.store (headerField 0) (.const 1#64))::
    .command (.store (headerField 8) (.op .add [localVar "raw",.const 0#64]))::afterFirstStores := by
  simp only [afterFirstStores,afterClear,afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,
    Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    CallPrefix.cut,show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,headerField,localVar]
  rfl

/-- The genuine normal clear derives its exact memory effect and actual
remaining action execution, with all caller globals/locals restored. -/
theorem clear_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (execution : CallPrefix.Execution (headerEntry source pointer record heap) afterHeader current) :
    CallPrefix.Execution (clearedHeader source pointer record heap) afterClear current := by
  rw [clearing_action] at execution
  obtain ⟨middle,normal,next⟩:=execution.command_next zeroHeader afterClear
  let allocated:=headerEntry source pointer record heap
  have hCell : allocated.locals.lookup (ofString "h")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have args : evalListHOLFinite allocated (h:=fun address=>Classical.propDecidable (allocated.memaddrs address))
      [localVar "h",.const 248#64]=some (Zero.values heap 248):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hCell,Zero.values]
  have mapped (offset : Nat) (inside : offset+8≤248) (multiple : offset%8=0) : allocated.memaddrs (byteAddress heap offset):=
    AllocatedBytes.word_mapped allocated heap 248 offset domain arena (by omega) aligned multiple
  obtain ⟨funded,same⟩:=Zero.call_normal allocated middle [localVar "h",.const 248#64] heap 248 args
    (Zero.original_code source.code installed) (by decide) (by decide) aligned mapped normal
  rw [same] at next
  exact next

theorem cleared_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (slot : Nat) (inside : slot<31) : (clearedHeader source pointer record heap).memory (heap+BitVec.ofNat 64 (8*slot))=.word 0#64:=
  MutableTable.ZeroWords.final_cell source.memory heap 248 slot (by omega)

theorem cleared_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap query : BitVec 64)
    (arena : AllocatedBytes.Arena heap 248) (before : query.toNat<heap.toNat) :
    (clearedHeader source pointer record heap).memory query=source.memory query := by
  apply Zero.final_memory_away
  intro offset inside same
  have number:=byteAddress_toNat heap offset (by have upper:=arena.upper; omega)
  have numeric:=congrArg BitVec.toNat same
  rw [number] at numeric
  omega

theorem first_stores_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0) :
    evaluateHOLFiniteState (clearedHeader source pointer record heap) (.store (headerField 0) (.const 1#64))=
      (none,putHeader (clearedHeader source pointer record heap) heap 0 1#64) ∧
    evaluateHOLFiniteState (putHeader (clearedHeader source pointer record heap) heap 0 1#64)
      (.store (headerField 8) (.op .add [localVar "raw",.const 0#64]))=(none,firstStored source pointer record heap) := by
  let cleared:=clearedHeader source pointer record heap
  let first:=putHeader cleared heap 0 1#64
  have hCell : cleared.locals.lookup (ofString "h")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have rawCell : first.locals.lookup (ofString "raw")=some (.val (.word (pointer+62#64))):=
    (bind_lookup_other _ "h" "raw" heap (by decide)).trans (bind_lookup_same _ _ _)
  have addressRead (state : PanSemStateFiniteExact 64 Guest.HostMemory) (cell : state.locals.lookup (ofString "h")=some (.val (.word heap))) (offset : Nat) :
      eval state (headerField offset)=some (.val (.word (heap+BitVec.ofNat 64 offset))) := by
    simp [eval,headerField,evalHOLExact,evalListHOLExact,localVar,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rawRead : eval first (.op .add [localVar "raw",.const 0#64])=some (.val (.word (pointer+62#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,rawCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact ⟨StoreWord.execute cleared _ _ _ 1#64 (addressRead cleared hCell 0) rfl
      (AllocatedBytes.word_mapped cleared heap 248 0 domain arena (by decide) aligned (by decide)),
    StoreWord.execute first _ _ _ (pointer+62#64) (addressRead first hCell 8) rawRead
      (AllocatedBytes.word_mapped first heap 248 8 domain arena (by decide) aligned (by decide))⟩

/-- The actual prefix installs its real version flag and parent-hash
pointer in the cleared fresh header, retaining its original continuation. -/
theorem first_stores {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ heap.toNat+248≤2952790016 ∧ AllocatedBytes.Arena heap 248 ∧ heap.toNat%8=0 ∧
      boundary+32≤heap.toNat ∧ CallPrefix.Execution (firstStored source pointer record heap) afterFirstStores current := by
  obtain ⟨heap,heapCell,room,arena,aligned,before,frame,next⟩:=first_allocation data execution
  have cleared:=clear_from_execution source current pointer record heap data.arena.code data.arena.domain arena aligned next
  rw [first_store_actions] at cleared
  obtain ⟨first,second⟩:=first_stores_execute source pointer record heap data.arena.domain arena aligned
  have afterVersion:=cleared.command_known _ _ first
  have afterParent:=afterVersion.command_known _ _ second
  exact ⟨heap,heapCell,room,arena,aligned,before,afterParent⟩


/-- All header cells have their actual initial value after the first stores. -/
def initialHeaderWord (pointer : BitVec 64) (slot : Nat) : BitVec 64:=
  if slot=1 then pointer+62#64 else if slot=0 then 1#64 else 0#64

theorem first_stored_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (arena : AllocatedBytes.Arena heap 248) (slot : Nat) (inside : slot<31) :
    (firstStored source pointer record heap).memory (heap+BitVec.ofNat 64 (8*slot))=.word (initialHeaderWord pointer slot) := by
  have number:=byteAddress_toNat heap (8*slot) (by have upper:=arena.upper; omega)
  have plus8:=byteAddress_toNat heap 8 (by have upper:=arena.upper; omega)
  have same0 : (heap+BitVec.ofNat 64 (8*slot)=heap)↔slot=0:=by
    constructor
    · intro same
      have numeric:=congrArg BitVec.toNat same
      change (heap+BitVec.ofNat 64 (8*slot)).toNat=heap.toNat+8*slot at number
      omega
    · intro zero; subst slot; simp
  have same1 : (heap+BitVec.ofNat 64 (8*slot)=heap+8#64)↔slot=1:=by
    constructor
    · intro same
      have numeric:=congrArg BitVec.toNat same
      change (heap+BitVec.ofNat 64 (8*slot)).toNat=heap.toNat+8*slot at number
      change (heap+8#64).toNat=heap.toNat+8 at plus8
      omega
    · intro one; subst slot; rfl
  simp only [firstStored,putHeader,StoreWord.put,BitVec.add_zero,same0,same1,
    cleared_cells source pointer record heap slot inside,initialHeaderWord]
  split_ifs <;>rfl

theorem first_stored_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap query : BitVec 64)
    (arena : AllocatedBytes.Arena heap 248) (before : query.toNat<heap.toNat) :
    (firstStored source pointer record heap).memory query=source.memory query := by
  have plus8:=byteAddress_toNat heap 8 (by have upper:=arena.upper; omega)
  have different0 : query≠heap:=by intro same; subst query; omega
  have different1 : query≠heap+8#64:=by
    intro same
    have number:=congrArg BitVec.toNat same
    change (heap+8#64).toNat=heap.toNat+8 at plus8
    omega
  simp only [firstStored,putHeader,StoreWord.put,BitVec.add_zero,if_neg different0,if_neg different1]
  exact cleared_older source pointer record heap query arena before

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.clearing_action
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_store_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.clear_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.cleared_cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.cleared_older
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_stores_execute
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_stores

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_stored_cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.first_stored_older
