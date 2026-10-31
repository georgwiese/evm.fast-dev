import InitECandidate.Solver.Input.CurrentVerify.TransactionFields
import InitECandidate.Solver.Rlp.CurrentDecodeCall
import InitECandidate.Solver.Input.NoReturnDecision
import InitECandidate.Solver.Rlp.CurrentSlicesReachedCost
import InitECandidate.Solver.Rlp.CurrentSlicesCall
import InitECandidate.Solver.Rlp.ListItemAt
import InitECandidate.Solver.Rlp.ListItemsTotal
import InitECandidate.Solver.Rlp.SliceRecordsFrame
import InitECandidate.Solver.Input.BufferDynamicCost
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.ClockCostPotentialLoop
import InitECandidate.Solver.Input.CallPrefixAllocation
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.WitnessRadix.RestoreLookup
import InitECandidate.Solver.Input.LoopInvariantNoControl
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Rlp.CurrentSlicesPersistentFrame
import InitECandidate.Solver.Input.PersistentAllocationFrame
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.WordQuadEnvironment
import InitECandidate.Solver.Input.StoreBoundedNormal
import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.ClockCostAssignedCurrent
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.RlpWrite.U256Shape
import InitECandidate.Solver.Input.ScopedNoLoopControl
import InitECandidate.Solver.Input.NoReturnScoped
import InitECandidate.Solver.Input.WordStoreNormal

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Retain a smaller actual protected frontier without changing the
observed heap, runtime or normal execution used to derive the frame. -/
theorem PersistentNormalFrame.lower_frontier {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {large small : BitVec 64}
    (frame : PersistentNormalFrame source target large) (before : small.toNat≤large.toNat) : PersistentNormalFrame source target small := by
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  exact ⟨⟨next,cell,arena,bounded,aligned,Nat.le_trans before grows⟩,frame.metadata,frame.globals,
    by intro query lower; exact frame.memory query (Nat.lt_of_lt_of_le lower before)⟩

end InitECandidate.Solver.Input

namespace InitECandidate.Solver.Input.CurrentVerify.BlobHashes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

abbrev resultShape : ShapeHOL:=.comb [.one,.one]
def body : ProgHOL 64:=match Guest.Software.guestFn_decode_blob_hashes with | .function fn=>progToHOL fn.body | _=>.skip
def sliceArguments : List (ExpHOL 64):=[localVar "p",localVar "len"]
def afterSlices : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def allocationArguments : List (ExpHOL 64):=[.panop .mul [.rfield 1 (localVar "lst"),.const 32#64]]
def afterAllocation : ProgHOL 64:=match afterSlices with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loopAndReturn : ProgHOL 64:=match afterAllocation with | .dec _ _ _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .lower (localVar "i") (.rfield 1 (localVar "lst"))
def iteration : ProgHOL 64:=match loopAndReturn with | .seq (.while _ rest) _=>rest | _=>.skip
def readerArguments : List (ExpHOL 64):=[.rfield 0 (localVar "lst"),localVar "i",.const 32#64]
def copyArguments : List (ExpHOL 64):=[.op .add [localVar "buf",.panop .mul [localVar "i",.const 32#64]],localVar "h",.const 32#64]
def copyCall : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") copyArguments
def increment : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def footer : ProgHOL 64:=.seq copyCall increment

set_option maxRecDepth 100000 in
theorem shapes : body=.decCall (ofString "lst") resultShape (ofString "rlp_list_to_slices") sliceArguments afterSlices ∧
    afterSlices=.decCall (ofString "buf") .one (ofString "alloc") allocationArguments afterAllocation ∧
    afterAllocation=.dec (ofString "i") .one (.const 0#64) loopAndReturn ∧
    loopAndReturn=.seq (.while test iteration) (.return (.rstruct [localVar "buf",.rfield 1 (localVar "lst")])) ∧
    iteration=.decCall (ofString "h") .one (ofString "tx_fixed_bytes") readerArguments footer := by
  simp only [body,afterSlices,afterAllocation,loopAndReturn,iteration,test,sliceArguments,allocationArguments,readerArguments,footer,copyCall,copyArguments,increment,resultShape,localVar,
    Guest.Software.guestFn_decode_blob_hashes,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  trivial

/-- Real stored slice rows and the allocated output buffer during copying.
The item geometry comes from the actual earlier RLP converter. -/
structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array buffer count : BitVec 64) (items : List Rlp.ListItem) where
  index : BitVec 64
  arena : Rlp.LiveArena source
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count)
  bufferCell : source.locals.lookup (ofString "buf")=some (.val (.word buffer))
  bounded : index.toNat≤count.toNat
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  totalBytes : (items.map Rlp.ListItem.size).sum=length.toNat
  records : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+16*count.toNat≤buffer.toNat
  bufferArena : AllocatedBytes.Arena buffer (32*count.toNat)
  bufferAligned : buffer.toNat%8=0
  bufferBound : buffer.toNat+32*count.toNat≤2952790016
  spans : ∀ index item,items[index]?=some item →
    item.total.toNat=item.size ∧ (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat<2^64

/-- Exact arithmetic of the actual32-byte destination slot. -/
theorem LoopModel.destination {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat) :
    (buffer+model.index*32#64).toNat=buffer.toNat+32*model.index.toNat ∧
      (buffer+model.index*32#64).toNat%8=0 ∧ (buffer+model.index*32#64).toNat+32<2^64 := by
  have room:=model.bufferBound
  have product : (model.index*32#64).toNat=32*model.index.toNat:=by
    rw [BitVec.toNat_mul]
    change (model.index.toNat*32)%2^64=32*model.index.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have number : (buffer+model.index*32#64).toNat=buffer.toNat+32*model.index.toNat:=by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  exact ⟨number,by rw [number]; have aligned:=model.bufferAligned; omega,by rw [number]; omega⟩

theorem LoopModel.select {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat) :
    ∃ item,items[model.index.toNat]?=some item := by
  have inside : model.index.toNat<items.length:=by rw [←model.countExact]; exact active
  exact ⟨items[model.index.toNat],List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩⟩

/-- Each actual array row supplies the genuine fixed32 reader entry. -/
theorem LoopModel.reader_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[model.index.toNat]?=some item) :
    ∃ callee,evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) readerArguments=
        some [.val (.word array),.val (.word model.index),.val (.word 32#64)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "tx_fixed_bytes") [.val (.word array),.val (.word model.index),.val (.word 32#64)]=
        some (TransactionFields.body .fixed,callee,.one) ∧
      TransactionNumbers.Row (callEntryStateHOLFinite source callee) array model.index (Rlp.Slices.itemPointer pointer items model.index.toNat) item.total ∧
      callee.lookup (ofString "width")=some (.val (.word 32#64)) := by
  obtain ⟨callee,called,aCell,iCell,widthCell⟩:=word_triple_environment source.code.lookup (ofString "tx_fixed_bytes") (ofString "arr") (ofString "i") (ofString "width")
    (TransactionFields.body .fixed) .one array model.index 32#64 (by decide) (by decide) (by decide)
    (TransactionFields.original_code .fixed source.code model.arena.code)
  have words:=Rlp.Slices.Records.at source.memory array pointer items model.records model.index.toNat item selected
  have product : BitVec.ofNat 64 (16*model.index.toNat)=model.index*16#64:=by
    simp [BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]
  rw [product] at words
  have firstMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*model.index.toNat) model.arena.domain model.arrayArena (by omega) model.arrayAligned (by omega)
  have secondMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*model.index.toNat+8) model.arena.domain model.arrayArena (by omega) model.arrayAligned (by omega)
  simp only [byteAddress,BitVec.ofNat_add,product] at firstMapped secondMapped
  exact ⟨callee,by simp [readerArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.listCell,model.indexCell,Rlp.Slices.result],called,
    ⟨model.arena.of_frame rfl,aCell,iCell,firstMapped,by
      change source.memaddrs (array+model.index*16#64+8#64)
      simpa only [BitVec.add_assoc] using secondMapped,words.1,words.2,(model.spans _ _ selected).2⟩,widthCell⟩

/-- A literal32-byte copy and increment cost at most42 ticks on every
outcome, independently of whether the copied source is mapped. -/
theorem footer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source footer).2.clock≤42 := by
  have copyPrice:=BufferDynamicCost.copy_cost source (.op .add [localVar "buf",.panop .mul [localVar "i",.const 32#64]]) (localVar "h") (.const 32#64) 32 installed (by decide) rfl
  exact ClockCost.sequence_current source copyCall increment 42 0 copyPrice (ClockCost.assign source.code _ _)

/-- The real selected row, its fixed reader and memcpy are charged once. -/
theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[model.index.toNat]?=some item) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤60*item.size+54 := by
  obtain ⟨callee,args,called,row,widthCell⟩:=model.reader_entry active item selected
  have price:=TransactionFields.body_cost (callEntryStateHOLFinite source callee) .fixed _ _ row.arena row.fits row.arguments
  rw [shapes.2.2.2.2]
  have total:=ClockCost.scoped_reached_current source "h" .one (ofString "tx_fixed_bytes") readerArguments _ (TransactionFields.body .fixed) footer callee .one
    (60*item.total.toNat+11) 42 args called price (by
      intro child returned normal checked
      have codeEq:=(evaluation_fields (callEntryStateHOLFinite source callee) child (TransactionFields.body .fixed) (some (.returned returned)) normal).2.2.2
      exact footer_cost (CallNormal.continuationEntry source child "h" returned) (by change OriginalCode.Installed child.code; rw [codeEq]; exact model.arena.code))
  rw [(model.spans _ _ selected).1] at total
  omega

/-- A normally continuing actual iteration retains its slice array and
all earlier input, and advances exactly one initialized output slot. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat)
    (normal : evaluateHOLFiniteState source iteration=(none,target)) :
    ∃ next : LoopModel target pointer length array buffer count items,next.index=model.index+1#64 ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query := by
  obtain ⟨item,selected⟩:=model.select active
  obtain ⟨callee,args,called,row,widthCell⟩:=model.reader_entry active item selected
  rw [shapes.2.2.2.2] at normal
  obtain ⟨funded,child,returned,inner,fieldRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source target "h" .one (ofString "tx_fixed_bytes")
    readerArguments _ (TransactionFields.body .fixed) footer callee .one args called normal
  obtain ⟨header,valid,valueEq,parseFrame⟩:=TransactionFields.body_fixed_normal (callEntryStateHOLFinite source callee) child _ _ 32#64 row.arena row.fits row.arguments widthCell returned fieldRun
  let resumed:=CallNormal.continuationEntry source child "h" returned
  have resumed_saved (name : String) (different : ofString "h"≠ofString name) :
      resumed.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    simp [resumed,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have hCell : resumed.locals.lookup (ofString "h")=some (.val (.word (Rlp.Slices.itemPointer pointer items model.index.toNat+header))):=by
    simp [resumed,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueEq]
  have iCell : resumed.locals.lookup (ofString "i")=some (.val (.word model.index)):= (resumed_saved "i" (by decide)).trans model.indexCell
  have bCell : resumed.locals.lookup (ofString "buf")=some (.val (.word buffer)):= (resumed_saved "buf" (by decide)).trans model.bufferCell
  obtain ⟨copied,copyRun,incrementRun⟩:=sequence_none resumed inner copyCall increment continued
  have copyArgs : evalListHOLFinite resumed (h:=fun query=>Classical.propDecidable (resumed.memaddrs query)) copyArguments=
      some (CopyGeneral.values (buffer+model.index*32#64) (Rlp.Slices.itemPointer pointer items model.index.toNat+header) 32):=by
    simp [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,bCell,iCell,hCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have installed : OriginalCode.Installed resumed.code:=by
    change OriginalCode.Installed child.code
    rw [MemoryMetadata.code parseFrame.metadata]
    exact model.arena.code
  obtain ⟨copyFrame,copyLocals⟩:=CopyAny.call_span_normal resumed copied (buffer+model.index*32#64)
    (Rlp.Slices.itemPointer pointer items model.index.toNat+header) 32 (by decide) copyArguments copyArgs installed copyRun
  have copiedIndex : copied.locals.lookup (ofString "i")=some (.val (.word model.index)):=by rw [copyLocals]; exact iCell
  have read : eval copied (.op .add [localVar "i",.const 1#64])=some (.val (.word (model.index+1#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,copiedIndex,valueIsWord,valueWord,wordOpHOL,wordOp]
  have incrementEq:=assign_none copied inner "i" _ _ read incrementRun
  have metadata : MemoryMetadata.erase target=MemoryMetadata.erase source:=by
    rw [endpoint,incrementEq]
    have copiedMetadata : MemoryMetadata.erase copied=MemoryMetadata.erase resumed:=copyFrame.fields
    exact copiedMetadata.trans parseFrame.metadata
  have older (query : BitVec 64) (before : query.toNat<buffer.toNat) : target.memory query=source.memory query:=by
    obtain ⟨number,aligned,fits⟩:=model.destination active
    have away : CopyGeneral.Away (buffer+model.index*32#64) query 32:=CopyGeneral.Away.after _ _ _ aligned fits (by rw [number]; omega)
    rw [endpoint,incrementEq]
    change copied.memory query=source.memory query
    exact (copyFrame.memory query away).trans (parseFrame.outside query (Or.inl (by have cap:=model.bufferBound; omega)))
  have saved (name : String) (notI : ofString "i"≠ofString name) (notH : ofString "h"≠ofString name) :
      target.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [endpoint,incrementEq]
    exact (restore_lookup_other source _ "h" name (Ne.symm notH)).trans
      ((bind_lookup_other copied "i" name _ notI).trans
        ((congrArg (fun locals=>locals.lookup (ofString name)) copyLocals).trans (resumed_saved name notH)))
  have nextIndex : target.locals.lookup (ofString "i")=some (.val (.word (model.index+1#64))):=by
    rw [endpoint,incrementEq]
    exact (restore_lookup_other source _ "h" "i" (by decide)).trans (bind_lookup_same _ _ _)
  have indexNumber : (model.index+1#64).toNat=model.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; have upper:=count.isLt; omega)]
    rfl
  have records:=model.records.of_interval source target array pointer items (by
    rw [←model.countExact]; have upper:=model.arrayArena.upper; omega) (by
      intro query above before
      apply older query
      rw [←model.countExact] at before
      have arrayBefore:=model.arrayBefore
      omega)
  let next : LoopModel target pointer length array buffer count items:={model with
    index:=model.index+1#64,arena:=model.arena.of_metadata metadata,indexCell:=nextIndex
    listCell:=(saved "lst" (by decide) (by decide)).trans model.listCell
    bufferCell:=(saved "buf" (by decide) (by decide)).trans model.bufferCell
    bounded:=by rw [indexNumber]; omega,records:=records }
  exact ⟨next,rfl,metadata,older⟩

/-- Remaining parse/copy work: each actual row pays for its own byte
extent and one constant-sized copy/caller/loop overhead. -/
def charge : List Rlp.ListItem→Nat→Nat
  | [],_=>0
  | item::items,0=>60*item.size+55+charge items 0
  | _::items,index+1=>charge items index

theorem charge_step (items : List Rlp.ListItem) (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) :
    charge items index=60*item.size+55+charge items (index+1) := by
  induction items generalizing index with
  | nil=>simp at selected
  | cons head items ih=>
    cases index with
    | zero=>
      have same : head=item:=by simpa using selected
      subst item
      rfl
    | succ index=>exact ih index (by simpa using selected)

theorem charge_zero (items : List Rlp.ListItem) : charge items 0=60*(items.map Rlp.ListItem.size).sum+55*items.length := by
  induction items with
  | nil=>rfl
  | cons item items ih=>simp only [charge,List.map_cons,List.sum_cons,List.length_cons,ih]; omega

theorem charge_le_zero (items : List Rlp.ListItem) (index : Nat) : charge items index≤charge items 0 := by
  induction items generalizing index with
  | nil=>simp [charge]
  | cons item items ih=>
    cases index with
    | zero=>exact Nat.le_refl _
    | succ index=>simp only [charge]; have bound:=ih index; omega

theorem LoopModel.charge_bound {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) : charge items model.index.toNat≤115*length.toNat := by
  have bound:=charge_le_zero items model.index.toNat
  rw [charge_zero,model.totalBytes,←model.countExact] at bound
  have countBound:=model.countBound
  omega

def LoopModel.clocked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (clock : Nat) :
    LoopModel {source with clock:=clock} pointer length array buffer count items :=
  {model with arena:=model.arena.of_frame rfl}

theorem test_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) :
    eval source test=some (.val (.word (if model.index.toNat<count.toNat then 1#64 else 0#64))) := by
  simp [eval,test,evalHOLExact,toExact,localVar,model.indexCell,model.listCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

theorem active_of_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.index.toNat<count.toNat := by
  have expected:=test_read model
  by_contra inactive
  rw [if_neg inactive] at expected
  have same : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero same

theorem iteration_limit : LocalPrefix (ofString "lst") iteration := by
  rw [shapes.2.2.2.2]
  exact .decCall (ofString "h") .one (ofString "tx_fixed_bytes") readerArguments (by decide)
    (.seq (.call none (ofString "memcpy") copyArguments (by intro name impossible; cases impossible)) (.assign _ _ (by decide)))

/-- Linear full-loop allowance from the actual remaining rows. Continuing
bodies spend their own row charge; aborted bodies fit the remaining budget. -/
theorem loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤charge items model.index.toNat := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current pointer length array buffer count items)
  let allowance:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>charge items (CounterFlow.counterWord current (ofString "i")).toNat
  have allowance_model (current : PanSemStateFiniteExact 64 Guest.HostMemory) (live : LoopModel current pointer length array buffer count items) :
      allowance current=charge items live.index.toNat:=by simp [allowance,CounterFlow.counterWord,live.indexCell,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
      current.clock-output.2.clock≤allowance current ∧
        ((output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ current.clock-output.2.clock+allowance output.2≤allowance current):=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=active_of_test live word read nonzero
    obtain ⟨item,selected⟩:=live.select active
    let entered:=live.clocked (current.clock-1)
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have price:=iteration_cost entered active item selected
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
    change current.clock-1-output.2.clock≤60*item.size+54 at price
    change output.2.clock≤current.clock-1 at forward
    have paid : current.clock-output.2.clock≤60*item.size+55:=by omega
    have charged:=charge_step items live.index.toNat item selected
    refine ⟨?_,?_⟩
    · change current.clock-output.2.clock≤allowance current
      rw [allowance_model current live,charged]
      omega
    intro continuing
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((iteration_limit.summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,metadata,memory⟩:=iteration_normal entered active run
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have bound:=count.isLt; omega)]
      rfl
    have nextNumber : next.index.toNat=live.index.toNat+1:=(congrArg BitVec.toNat indexEq).trans number
    refine ⟨⟨next⟩,?_⟩
    change current.clock-output.2.clock+allowance output.2≤allowance current
    rw [allowance_model current live,allowance_model output.2 next,nextNumber,charged]
    omega
  have priced:=ClockCost.potential_loop source.code test iteration invariant allowance step source rfl ⟨model⟩
  rwa [allowance_model source model] at priced

/-- All real byte extents are charged once, giving a linear loop budget. -/
theorem loop_linear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤115*length.toNat :=
  (loop_cost model).trans model.charge_bound

/-- Actual normal loop completion retains the allocated buffers, restored
runtime metadata, unchanged earlier input and the final checked row count. -/
theorem loop_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items)
    (normal : evaluateHOLFiniteState source (.while test iteration)=(none,target)) :
    ∃ final : LoopModel target pointer length array buffer count items,final.index.toNat=count.toNat ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel current pointer length array buffer count items,
    MemoryMetadata.erase current=MemoryMetadata.erase source ∧ ∀ query : BitVec 64,query.toNat<buffer.toNat→current.memory query=source.memory query
  have initial : invariant source:=⟨model,rfl,by intros; rfl⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,post)→invariant post:=by
    intro current codeEq valid word read nonzero funded post run
    obtain ⟨live,metadata,memory⟩:=valid
    let entered:=live.clocked (current.clock-1)
    obtain ⟨next,indexEq,nextMetadata,nextMemory⟩:=iteration_normal entered (active_of_test live word read nonzero) run
    exact ⟨next,nextMetadata.trans metadata,fun query before=>(nextMemory query before).trans (memory query before)⟩
  obtain ⟨final,metadata,memory⟩:=loop_invariant_no_control source.code test iteration (fun current=>(iteration_limit.summary_full current).2.2)
    invariant step source target rfl initial normal
  have exited:=loop_normal_exit test iteration (fun current=>(iteration_limit.summary_full current).2.2.1) source target normal
  have expected:=test_read final
  have finished : final.index.toNat=count.toNat:=by
    by_cases active : final.index.toNat<count.toNat
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact (by decide : (0#64 : BitVec 64)≠1#64) impossible |>.elim
    · have bounded:=final.bounded; omega
  exact ⟨final,finished,metadata,memory⟩

/-- Current physical blob-decoder entry, before its own slice/output
allocations. Input validity or a future normal parser return is not assumed. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64) : Prop where
  arena : Rlp.LiveArena source
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  inputBefore : pointer.toNat+length.toNat≤heap.toNat

/-- The already observed real slice result, with its current next heap.
This stage contains no output-allocation room or later loop hypothesis. -/
structure Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array buffer count : BitVec 64) (items : List Rlp.ListItem) where
  arena : Rlp.LiveArena source
  listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count)
  itemModel : Rlp.ListItems source pointer length.toNat items
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  records : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+16*count.toNat≤buffer.toNat
  inputBefore : pointer.toNat+length.toNat≤array.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))
  heapArena : AllocatedBytes.Arena buffer 0
  heapBound : buffer.toNat≤2952790016
  heapAligned : buffer.toNat%8=0

/-- All prepared geometry is supplied by this actual current conversion. -/
def prepared_from_converter {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap count : BitVec 64} {items : List Rlp.ListItem}
    (data : Entry source pointer length heap)
    (itemModel : Rlp.ListItems target pointer length.toNat items) (countExact : count.toNat=items.length) (countBound : count.toNat≤length.toNat)
    (records : Rlp.Slices.Records target.memory heap pointer items) (room : heap.toNat+16*count.toNat≤2952790016)
    (arena : Rlp.LiveArena target)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) :
    Prepared (CallNormal.continuationEntry source target "lst" (Rlp.Slices.result heap count)) pointer length heap (PersistentAlloc.rounded heap (count*16#64)) count items := by
  let ready:=CallNormal.continuationEntry source target "lst" (Rlp.Slices.result heap count)
  have amount : (count*16#64).toNat=16*count.toNat:=by
    rw [BitVec.toNat_mul]
    change (count.toNat*16)%2^64=16*count.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have guards:=PersistentAlloc.guards heap (count*16#64) (by rw [amount]; exact room)
  have grows : heap.toNat+16*count.toNat≤(PersistentAlloc.rounded heap (count*16#64)).toNat:=by
    have bound:=guards.2.2.1
    rw [amount] at bound
    exact bound
  have upper:=guards.2.2.2.1
  exact {
    arena:=arena.of_frame rfl
    listCell:=by simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    itemModel:=Rlp.ListItems.transport target ready pointer length.toNat items itemModel length.isLt (by intros; rfl)
    countExact:=countExact,countBound:=countBound,records:=records
    arrayArena:=⟨data.heapArena.lower,by omega⟩,arrayAligned:=data.heapAligned,arrayBefore:=grows,inputBefore:=data.inputBefore
    heapCell:=by
      change target.globals.lookup (ofString "heap_ptr")=_
      rw [globals]
      simp [HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=data.heapArena.lower; omega,by omega⟩
    heapBound:=upper,heapAligned:=guards.2.2.2.2 }

def allocationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer count : BitVec 64) :=
  setVarHOLFinite (ofString "buf") (.val (.word buffer)) (PersistentAlloc.post {source with clock:=source.clock-1} buffer (count*32#64))

def loopEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer count : BitVec 64) :=
  QueryBranch.bind (allocationEntry source buffer count) "i" 0#64

theorem Prepared.amount {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) : (count*32#64).toNat=32*count.toNat := by
  have countBound:=data.countBound
  have inputBefore:=data.inputBefore
  have arrayBefore:=data.arrayBefore
  have heapBound:=data.heapBound
  rw [BitVec.toNat_mul]
  change (count.toNat*32)%2^64=32*count.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Real returned allocator room initializes the physical loop, including
empty arrays; its count/shape/source facts come from the earlier converter. -/
def Prepared.loop_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (room : buffer.toNat+(count*32#64).toNat≤2952790016) :
    LoopModel (loopEntry source buffer count) pointer length array buffer count items := by
  rw [data.amount] at room
  let entered:=loopEntry source buffer count
  have live : Rlp.LiveArena entered:=by
    apply data.arena.of_cursors (target:=entered) rfl rfl
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide]
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide]
  exact {
    index:=0#64,arena:=live,indexCell:=bind_lookup_same _ _ _
    listCell:=by
      simpa [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "i"≠ofString "lst" from by decide,show ofString "buf"≠ofString "lst" from by decide] using data.listCell
    bufferCell:=by
      simp [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "i"≠ofString "buf" from by decide]
    bounded:=by simp,countExact:=data.countExact,countBound:=data.countBound
    totalBytes:=data.itemModel.total_size source pointer length.toNat items,records:=data.records
    arrayArena:=data.arrayArena,arrayAligned:=data.arrayAligned,arrayBefore:=data.arrayBefore
    bufferArena:=⟨data.heapArena.lower,by omega⟩,bufferAligned:=data.heapAligned,bufferBound:=room
    spans:=by
      intro index item selected
      have fields:=data.itemModel.at_span source pointer length.toNat items index item selected (by
        have before:=data.inputBefore; have bound:=array.isLt; omega)
      exact ⟨fields.1,fields.2.2.2⟩ }

theorem after_allocation_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (room : buffer.toNat+(count*32#64).toNat≤2952790016) :
    (allocationEntry source buffer count).clock-(evaluateHOLFiniteState (allocationEntry source buffer count) afterAllocation).2.clock≤115*length.toNat := by
  rw [shapes.2.2.1]
  apply ClockCost.declared_current (allocationEntry source buffer count) "i" (.const 0#64) 0#64 loopAndReturn (115*length.toNat) rfl
  rw [shapes.2.2.2.1]
  exact ClockCost.sequence_current (loopEntry source buffer count) _ _ (115*length.toNat) 0
    (loop_linear (data.loop_model room)) (ClockCost.returned _ _)

/-- The already reached scalar allocation returns its own room and exact
saved-caller state; this equality is obtained from the same callee run. -/
theorem allocation_return {source child : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (amountCell : callee.lookup (ofString "n")=some (.val (.word (count*32#64)))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PersistentAlloc.body=(some (.returned value),child)) :
    buffer.toNat+(count*32#64).toNat≤2952790016 ∧
      CallNormal.continuationEntry source child "buf" value=allocationEntry source buffer count := by
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child buffer (count*32#64)
    amountCell data.heapCell data.heapBound (Trap.original_code source.code data.arena.code) value normal
  refine ⟨room,?_⟩
  rw [answer]
  have changed:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString "buf") (.val (.word buffer)) {state with locals:=source.locals}) frame
  simpa only [CallNormal.continuationEntry,allocationEntry,emptyLocalsHOLFinite,PersistentAlloc.post,callEntryStateHOLFinite] using changed

theorem Prepared.allocation_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (count*32#64)) := by
  simp [allocationArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.listCell,Rlp.Slices.result,valueIsWord,valueWord,panOpHOL]

/-- Rejection/timeout remain in the real allocator price; only its own
normal return creates the loop entry and its remaining-work allowance. -/
theorem after_slices_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) :
    source.clock-(evaluateHOLFiniteState source afterSlices).2.clock≤115*length.toNat+2 := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*32#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [shapes.2.1]
  have price:=ClockCost.scoped_reached_current source "buf" .one (ofString "alloc") allocationArguments _ PersistentAlloc.body afterAllocation callee .one 1 (115*length.toNat)
    data.allocation_arguments called (PersistentAlloc.body_price source.code data.arena.code (callEntryStateHOLFinite source callee) rfl) (by
      intro child value normal checked
      obtain ⟨room,same⟩:=allocation_return data callee amountCell value normal
      change (CallNormal.continuationEntry source child "buf" value).clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source child "buf" value) afterAllocation).2.clock≤115*length.toNat
      rw [same]
      exact after_allocation_cost data room)
  omega

/-- Complete actual blob decoder, including both its real allocations,
all parsing/copy work and every stopped outcome. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (data : Entry source pointer length heap) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤186*length.toNat+6 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length):=by
    simp [sliceArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointerCell,data.lengthCell]
  rw [shapes.1]
  have price:=Rlp.CurrentSlices.scoped_frame_cost source pointer length heap data.arena data.heapCell data.heapBound data.inputBefore
    (by have before:=data.inputBefore; have bound:=data.heapBound; omega) "lst" sliceArguments afterSlices (115*length.toNat+2) args (by
      intro target items count model countExact countBound records room arena domain endian globals
      exact after_slices_cost (prepared_from_converter data model countExact countBound records room arena globals))
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "lst") resultShape (ofString "rlp_list_to_slices") sliceArguments afterSlices)).2.clock≤71*length.toNat+(115*length.toNat+2)+4 at price
  omega

/-- A real returning copy suffix exposes the genuine pair and retains all
metadata and every word before its allocated output buffer. -/
theorem after_allocation_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (room : buffer.toNat+(count*32#64).toNat≤2952790016)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (allocationEntry source buffer count) afterAllocation=(some (.returned value),target)) :
    value=Rlp.Slices.result buffer count ∧
      MemoryMetadata.erase target=MemoryMetadata.erase (allocationEntry source buffer count) ∧
      ∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query := by
  rw [shapes.2.2.1] at normal
  obtain ⟨inner,continued,restored⟩:=declaration_return_word (allocationEntry source buffer count) target "i" (.const 0#64) 0#64 loopAndReturn value rfl normal
  rw [shapes.2.2.2.1] at continued
  obtain ⟨middle,loopRun,returnRun⟩:=sequence_returned (loopEntry source buffer count) inner _ _ value
    ((LocalPrefix.loop test iteration_limit).summary_full _).2.1 continued
  obtain ⟨final,indexEq,metadata,memory⟩:=loop_normal (data.loop_model room) loopRun
  obtain ⟨read,returned⟩:=return_normal middle inner (.rstruct [localVar "buf",.rfield 1 (localVar "lst")]) value returnRun
  have expected : eval middle (.rstruct [localVar "buf",.rfield 1 (localVar "lst")])=some (Rlp.Slices.result buffer count):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,final.bufferCell,final.listCell,Rlp.Slices.result]
  have answer:=Option.some.inj (read.symm.trans expected)
  refine ⟨answer,?_,?_⟩
  · rw [restored,returned]
    exact metadata
  · intro query before
    rw [restored,returned]
    exact memory query before

/-- The same normal allocation which enters the loop establishes its room;
lexical restoration leaves the observed output and physical frame intact. -/
theorem after_slices_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned value),target)) :
    buffer.toNat+32*count.toNat≤2952790016 ∧ value=Rlp.Slices.result buffer count ∧
      MemoryMetadata.erase target=MemoryMetadata.erase (allocationEntry source buffer count) ∧
      PersistentNormalFrame source target buffer := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*32#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [shapes.2.1] at normal
  obtain ⟨funded,child,allocated,inner,allocationRun,checked,suffixRun,restored⟩:=
    CallNormal.scoped_normal source target "buf" .one (ofString "alloc") allocationArguments (PersistentAlloc.values (count*32#64))
      PersistentAlloc.body afterAllocation callee .one data.allocation_arguments called value normal
  obtain ⟨room,entryEq⟩:=allocation_return data callee amountCell allocated allocationRun
  rw [entryEq] at suffixRun
  obtain ⟨answer,metadata,memory⟩:=after_allocation_normal data room value suffixRun
  have allocationFrame:=PersistentAlloc.post_persistent_frame source buffer (count*32#64) data.heapArena room
  have entryFrame:=allocationFrame.of_erase source (PersistentAlloc.post source buffer (count*32#64)) source (allocationEntry source buffer count) buffer rfl rfl
  have suffixFrame:=entryFrame.after_memory source (allocationEntry source buffer count) inner buffer metadata memory
  have frame:=suffixFrame.of_erase source inner source target buffer rfl (by rw [restored]; rfl)
  refine ⟨?_,answer,?_,frame⟩
  · rwa [data.amount] at room
  · rw [restored]
    exact metadata

/-- The complete unchanged blob decoder returns its actual bounded, owned
buffer/count pair. Its two observed allocations preserve the entering input,
nonheap globals, bounded aligned heap and runtime metadata. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (data : Entry source pointer length heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ buffer count,value=Rlp.Slices.result buffer count ∧ count.toNat≤length.toNat ∧
      AllocatedBytes.Arena buffer (32*count.toNat) ∧ buffer.toNat%8=0 ∧
      (∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
        buffer.toNat+32*count.toNat≤next.toNat ∧ next.toNat≤2952790016 ∧ next.toNat%8=0) ∧
      PersistentNormalFrame source target heap := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length):=by
    simp [sliceArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointerCell,data.lengthCell]
  rw [shapes.1] at normal
  obtain ⟨funded,child,items,count,inner,model,countExact,countBound,records,room,arena,domain,endian,globals,window,metadata,above,clock,price,suffixRun,restored⟩:=
    Rlp.CurrentSlices.scoped_normal source target pointer length heap data.arena data.heapCell data.heapBound data.inputBefore
      (by have before:=data.inputBefore; have bound:=data.heapBound; omega) "lst" sliceArguments afterSlices args value normal
  let ready:=CallNormal.continuationEntry source child "lst" (Rlp.Slices.result heap count)
  let buffer:=PersistentAlloc.rounded heap (count*16#64)
  have prepared:=prepared_from_converter data model countExact countBound records room arena globals
  obtain ⟨outputRoom,answer,outputMetadata,outputFrame⟩:=after_slices_normal prepared value suffixRun
  have converterFrame:=Rlp.CurrentSlices.persistent_frame_of_return source child heap count data.heapArena room metadata window
  have readyFrame:=converterFrame.of_erase source child source ready heap rfl rfl
  have grows : heap.toNat≤buffer.toNat:=by
    have next:=prepared.arrayBefore
    change heap.toNat+16*count.toNat≤buffer.toNat at next
    omega
  have composed:=readyFrame.trans source ready inner heap buffer outputFrame grows
  have frame:=composed.of_erase source inner source target heap rfl (by rw [restored]; rfl)
  have amount:=(prepared.amount)
  have allocationRoom : buffer.toNat+(count*32#64).toNat≤2952790016:=by rw [amount]; exact outputRoom
  have guards:=PersistentAlloc.guards buffer (count*32#64) allocationRoom
  have nextGlobals:=congrArg PanSemStateFiniteExact.globals outputMetadata
  change inner.globals=(allocationEntry ready buffer count).globals at nextGlobals
  have nextCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded buffer (count*32#64)))):=by
    rw [restored]
    change inner.globals.lookup (ofString "heap_ptr")=_
    rw [nextGlobals]
    simp [allocationEntry,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  exact ⟨buffer,count,answer,countBound,⟨prepared.heapArena.lower,by omega⟩,prepared.heapAligned,
    ⟨_,nextCell,by have next:=guards.2.2.1; rw [amount] at next; exact next,guards.2.2.2.1,guards.2.2.2.2⟩,frame⟩

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_blob_hashes")=some ([(ofString "p",.one),(ofString "len",.one)],body,resultShape) := by
  have checked:=OriginalCode.indexed code installed 277 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_blob_hashes) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,resultShape,
    Guest.Software.guestFn_decode_blob_hashes,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentVerify.BlobHashes

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.LoopModel.destination
#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.LoopModel.select
#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.LoopModel.reader_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.footer_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.iteration_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.iteration_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.charge_step

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.charge_zero

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.charge_le_zero

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.LoopModel.charge_bound

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.LoopModel.clocked

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.test_read

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.active_of_test

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.iteration_limit

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.loop_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.loop_linear

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.loop_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.prepared_from_converter

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.Prepared.amount

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.Prepared.loop_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.after_allocation_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.allocation_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.Prepared.allocation_arguments

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.after_slices_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.body_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.after_allocation_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.after_slices_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.BlobHashes.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.NestedLists
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

inductive Kind where | access | authorization

def declaration : Kind → Decl (BitVec 64)
  | .access=>Guest.Software.guestFn_decode_access_list
  | .authorization=>Guest.Software.guestFn_decode_authorizations

def body (kind : Kind) : ProgHOL 64:=match declaration kind with | .function fn=>progToHOL fn.body | _=>.skip
def iteration (kind : Kind) : ProgHOL 64:=match body kind with
  | .decCall _ _ _ _ (.decCall _ _ _ _ (.dec _ _ _ (.seq (.while _ step) _)))=>step | _=>.skip
def afterItem (kind : Kind) : ProgHOL 64:=match iteration kind with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterConversion (kind : Kind) : ProgHOL 64:=match afterItem kind with | .seq _ (.decCall _ _ _ _ rest)=>rest | _=>.skip
def fields (kind : Kind) : ProgHOL 64:=match afterConversion kind with | .seq _ rest=>rest | _=>.skip
def expected : Kind → BitVec 64 | .access=>2#64 | .authorization=>6#64
def errorCode : Kind → BitVec 64 | .access=>19#64 | .authorization=>20#64

def rowArguments : List (ExpHOL 64):=[
  .load .one (.op .add [.rfield 0 (localVar "lst"),.panop .mul [localVar "i",.const 16#64]]),
  .load .one (.op .add [.rfield 0 (localVar "lst"),.panop .mul [localVar "i",.const 16#64],.const 8#64])]
def payloadArguments : List (ExpHOL 64):=[.rfield 1 (localVar "it"),.rfield 2 (localVar "it")]

def itemGuard (kind : Kind) : ProgHOL 64:=TransactionFields.rejectUnequal (.rfield 0 (localVar "it")) (.const 1#64) (errorCode kind)
def countGuard (kind : Kind) : ProgHOL 64:=TransactionFields.rejectUnequal (.rfield 1 (localVar "ent")) (.const (expected kind)) (errorCode kind)

set_option maxRecDepth 100000 in
theorem shapes (kind : Kind) :
    iteration kind=.decCall (ofString "it") Rlp.Item.resultShape (ofString "rlp_item") rowArguments (afterItem kind) ∧
    afterItem kind=.seq (itemGuard kind) (.decCall (ofString "ent") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") payloadArguments (afterConversion kind)) ∧
    afterConversion kind=.seq (countGuard kind) (fields kind) := by
  cases kind <;> simp only [iteration,body,declaration,afterItem,afterConversion,fields,itemGuard,countGuard,expected,errorCode,
    rowArguments,payloadArguments,TransactionFields.rejectUnequal,localVar,Rlp.Item.resultShape,Rlp.Slices.resultShape,
    Guest.Software.guestFn_decode_access_list,Guest.Software.guestFn_decode_authorizations,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  all_goals trivial

/-- Physical entry to a nested item parse. No valid item, accepted shape,
or future successful allocation is required. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap : BitVec 64) : Prop where
  arena : Rlp.LiveArena source
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  inputBefore : pointer.toNat+length.toNat≤heap.toNat

/-- Actual freshly converted nested rows and their live heap frontier.
The arity check is kept separate until its real guard has passed. -/
structure Rows (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array next count : BitVec 64) (items : List Rlp.ListItem) where
  arena : Rlp.LiveArena source
  entryCell : source.locals.lookup (ofString "ent")=some (Rlp.Slices.result array count)
  model : Rlp.ListItems source pointer length.toNat items
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  records : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+16*count.toNat≤next.toNat
  inputBefore : pointer.toNat+length.toNat≤array.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word next))
  heapArena : AllocatedBytes.Arena next 0
  heapBound : next.toNat≤2952790016
  heapAligned : next.toNat%8=0

def rows_from_converter {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap count : BitVec 64} {items : List Rlp.ListItem}
    (entry : Entry source pointer length heap)
    (model : Rlp.ListItems target pointer length.toNat items) (countExact : count.toNat=items.length) (countBound : count.toNat≤length.toNat)
    (records : Rlp.Slices.Records target.memory heap pointer items) (room : heap.toNat+16*count.toNat≤2952790016)
    (arena : Rlp.LiveArena target)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) :
    Rows (CallNormal.continuationEntry source target "ent" (Rlp.Slices.result heap count)) pointer length heap (PersistentAlloc.rounded heap (count*16#64)) count items := by
  let ready:=CallNormal.continuationEntry source target "ent" (Rlp.Slices.result heap count)
  have amount : (count*16#64).toNat=16*count.toNat:=by
    rw [BitVec.toNat_mul]
    change (count.toNat*16)%2^64=16*count.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have guards:=PersistentAlloc.guards heap (count*16#64) (by rw [amount]; exact room)
  have grows:=guards.2.2.1
  rw [amount] at grows
  have upper:=guards.2.2.2.1
  exact {
    arena:=arena.of_frame rfl
    entryCell:=by simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    model:=Rlp.ListItems.transport target ready pointer length.toNat items model length.isLt (by intros; rfl)
    countExact:=countExact,countBound:=countBound,records:=records
    arrayArena:=⟨entry.heapArena.lower,by omega⟩,arrayAligned:=entry.heapAligned,arrayBefore:=grows,inputBefore:=entry.inputBefore
    heapCell:=by
      change target.globals.lookup (ofString "heap_ptr")=_
      rw [globals]
      simp [HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=entry.heapArena.lower; omega,by omega⟩
    heapBound:=upper,heapAligned:=guards.2.2.2.2 }

/-- The actual field-count rejection guard supplies the arity used to
price the remaining field operations. Rejecting outcomes spend no ticks. -/
theorem after_conversion_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (kind : Kind) (rows : Rows source pointer length array next count items) (price : Nat)
    (tail : count=expected kind→source.clock-(evaluateHOLFiniteState source (fields kind)).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (afterConversion kind)).2.clock≤price := by
  rw [(shapes kind).2.2]
  unfold countGuard TransactionFields.rejectUnequal
  have bounded:=ClockCost.stopping_guard_reached source (.cmp .notEqual (.rfield 1 (localVar "ent")) (.const (expected kind)))
    (.raise (ofString "TxErr") (.const (errorCode kind))) (fields kind) 0 price
    (raise_ne_none source _ _) (ClockCost.raised source.code _ _ source rfl) (by
      intro passed
      have countRead : eval source (.rfield 1 (localVar "ent"))=some (.val (.word count)):=by
        simp [eval,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
      have arity:=TransactionFields.reject_unequal_normal source source (.rfield 1 (localVar "ent")) (.const (expected kind))
        (errorCode kind) count (expected kind) countRead rfl passed
      exact tail arity)
  simpa only [Nat.zero_max] using bounded

/-- A real nested conversion supplies both its rows and its persistent
frame to the continuation price. No later field success is assumed. -/
theorem conversion_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (kind : Kind) (entry : Entry source pointer length heap) (price : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) payloadArguments=some (Rlp.Header.values pointer length))
    (tail : ∀ current next count items,Rows current pointer length heap next count items→count=expected kind→
      PersistentNormalFrame source current heap→
      (∀ key,key≠ofString "ent"→current.locals.lookup key=source.locals.lookup key)→
      current.clock-(evaluateHOLFiniteState current (fields kind)).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString "ent") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") payloadArguments (afterConversion kind))).2.clock≤71*length.toNat+price+4 := by
  have fits : pointer.toNat+length.toNat<2^64:=by have bound:=heap.isLt; have before:=entry.inputBefore; omega
  obtain ⟨callee,called,pointerCell,lengthCell⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") Rlp.Slices.body Rlp.Slices.resultShape pointer length
    (Rlp.Slices.original_code source.code entry.arena.code)
  have bodyPrice:=Rlp.CurrentSlices.body_cost (callEntryStateHOLFinite source callee) pointer length pointerCell lengthCell (entry.arena.of_frame rfl) fits entry.arena.code
  have actual:=ClockCost.scoped_reached_current source "ent" Rlp.Slices.resultShape (ofString "rlp_list_to_slices") payloadArguments _ Rlp.Slices.body (afterConversion kind) callee Rlp.Slices.resultShape
    (71*length.toNat+3) price args called bodyPrice (by
      intro child value normal checked
      obtain ⟨items,count,model,countExact,countBound,answer,records,room,arena,globals,window,metadata,above,spent⟩:=
        Rlp.CurrentSlices.body_normal (callEntryStateHOLFinite source callee) child pointer length heap pointerCell lengthCell (entry.arena.of_frame rfl)
          entry.heapCell entry.heapBound entry.inputBefore (by have before:=entry.inputBefore; have bound:=entry.heapBound; omega) value normal
      rw [answer]
      have rows:=rows_from_converter entry model countExact countBound records room arena globals
      have frame:=Rlp.CurrentSlices.persistent_frame_of_return source child heap count entry.heapArena room metadata window
      have continued:=frame.of_erase source child source (CallNormal.continuationEntry source child "ent" (Rlp.Slices.result heap count)) heap rfl rfl
      exact after_conversion_cost kind rows price (fun arity=>tail _ _ _ _ rows arity continued (by
        intro key other
        simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other])))
  omega

/-- Complete actual parse/conversion/shape prefix of either nested entry.
Only the real checked field state is supplied to its remaining-work price. -/
theorem iteration_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (kind : Kind) (entry : Entry source pointer length heap) (price : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length))
    (tail : ∀ current payloadPointer payloadLength next count items,
      payloadPointer.toNat+payloadLength.toNat≤pointer.toNat+length.toNat→payloadLength.toNat≤length.toNat→
      Rows current payloadPointer payloadLength heap next count items→count=expected kind→
      PersistentNormalFrame source current heap→
      (∀ key,key≠ofString "it"→key≠ofString "ent"→current.locals.lookup key=source.locals.lookup key)→
      current.clock-(evaluateHOLFiniteState current (fields kind)).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (iteration kind)).2.clock≤131*length.toNat+price+15 := by
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=entry.inputBefore; have bound:=heap.isLt; omega
  rw [(shapes kind).1]
  have priced:=Rlp.CurrentItem.scoped_valid_cost source pointer length entry.arena fits "it" rowArguments (afterItem kind) (71*length.toNat+price+4) args (by
    intro child value valid itemFrame
    obtain ⟨header,payload,flag,answer,small,positive,bounded,binary,listHeader⟩:=valid
    let ready:=setVarHOLFinite (ofString "it") value {child with locals:=source.locals}
    have runtime : MemoryMetadata.erase ready=MemoryMetadata.erase source:=itemFrame.metadata
    have globals:=congrArg PanSemStateFiniteExact.globals runtime
    change ready.globals=source.globals at globals
    have payloadNumber : (pointer+header).toNat=pointer.toNat+header.toNat:=by
      rw [BitVec.toNat_add_of_lt (by omega)]
    have contained : (pointer+header).toNat+payload.toNat≤pointer.toNat+length.toNat:=by rw [payloadNumber]; omega
    have payloadBound : payload.toNat≤length.toNat:=by omega
    have nextEntry : Entry ready (pointer+header) payload heap:=⟨entry.arena.of_metadata runtime,
      by rw [globals]; exact entry.heapCell,entry.heapArena,entry.heapBound,entry.heapAligned,by have before:=entry.inputBefore; omega⟩
    have frame:=PersistentNormalFrame.refl source heap entry.heapCell entry.heapArena entry.heapBound entry.heapAligned
    have parseFrame:=frame.after_memory source source ready heap runtime (by
      intro query before
      exact itemFrame.outside query (Or.inl (by have upper:=entry.heapBound; omega)))
    have payloadArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) payloadArguments=some (Rlp.Header.values (pointer+header) payload):=by
      simp [ready,payloadArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer,Rlp.Item.result]
    rw [(shapes kind).2.1]
    unfold itemGuard TransactionFields.rejectUnequal
    have conversion:=conversion_cost kind nextEntry price payloadArgs (by
      intro current next count items rows arity converted saved
      exact tail current (pointer+header) payload next count items contained payloadBound rows arity
        (parseFrame.trans source ready current heap heap converted (Nat.le_refl _)) (by
          intro key notIt notEnt
          rw [saved key notEnt]
          simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notIt,Ne.symm notIt]))
    have all:=ClockCost.stopping_guard_current ready (.cmp .notEqual (.rfield 0 (localVar "it")) (.const 1#64))
      (.raise (ofString "TxErr") (.const (errorCode kind))) _ 0 (71*payload.toNat+price+4)
      (raise_ne_none ready _ _) (ClockCost.raised ready.code _ _ ready rfl) conversion
    simp only [Nat.zero_max] at all
    exact all.trans (by omega))
  omega

/-- Every selected real nested row supplies the exact numeric/fixed
reader model in the actual ABI-created callee, independently of caller names. -/
theorem Rows.row {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (index : BitVec 64) (active : index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[index.toNat]?=some item)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "arr")=some (.val (.word array)))
    (indexCell : callee.lookup (ofString "i")=some (.val (.word index))) :
    TransactionNumbers.Row (callEntryStateHOLFinite source callee) array index (Rlp.Slices.itemPointer pointer items index.toNat) item.total := by
  have words:=Rlp.Slices.Records.at source.memory array pointer items rows.records index.toNat item selected
  have product : BitVec.ofNat 64 (16*index.toNat)=index*16#64:=by
    simp [BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]
  rw [product] at words
  have firstMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*index.toNat) rows.arena.domain rows.arrayArena (by omega) rows.arrayAligned (by omega)
  have secondMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*index.toNat+8) rows.arena.domain rows.arrayArena (by omega) rows.arrayAligned (by omega)
  simp only [byteAddress,BitVec.ofNat_add,product] at firstMapped secondMapped
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=rows.inputBefore; have upper:=array.isLt; omega
  exact ⟨rows.arena.of_frame rfl,arrayCell,indexCell,firstMapped,by
    change source.memaddrs (array+index*16#64+8#64)
    simpa only [BitVec.add_assoc] using secondMapped,words.1,words.2,
    (rows.model.at_span source pointer length.toNat items index.toNat item selected fits).2.2.2⟩

/-- Actual normal field readers restore the live row table and original
input while retaining their observed heap and caller tuple binding. -/
def Rows.reader_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (name : String) (value : ValueHOL 64)
    (other : ofString "ent"≠ofString name) (frame : Rlp.CurrentItem.Frame source target) :
    Rows (CallNormal.continuationEntry source target name value) pointer length array next count items := by
  let ready:=CallNormal.continuationEntry source target name value
  have metadata : MemoryMetadata.erase ready=MemoryMetadata.erase source:=frame.metadata
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change ready.globals=source.globals at globals
  have before : pointer.toNat+length.toNat≤2952790016:=by
    have inputBefore:=rows.inputBefore; have arrayBefore:=rows.arrayBefore; have heapBound:=rows.heapBound; omega
  have fits : pointer.toNat+length.toNat<2^64:=by omega
  have bytes:=Rlp.Slices.Window.bytes_before source ready 2952790016 2965299200 pointer length frame.outside.memory before fits
    (MemoryMetadata.domain metadata) (MemoryMetadata.endian metadata)
  exact {rows with
    arena:=rows.arena.of_metadata metadata
    entryCell:=by
      simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other] using rows.entryCell
    model:=rows.model.transport source ready pointer length.toNat items length.isLt bytes
    records:=rows.records.of_interval source ready array pointer items (by rw [←rows.countExact]; have bound:=rows.arrayArena.upper; omega) (by
      intro query above below
      apply frame.outside query (Or.inl ?_)
      rw [←rows.countExact] at below
      have arrayBefore:=rows.arrayBefore; have heapBound:=rows.heapBound; omega)
    heapCell:=by rw [globals]; exact rows.heapCell }

/-- A real output-record write retains both the earlier encoded input
and the separately allocated nested row array. -/
def Rows.of_window {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (lower upper : Nat)
    (metadata : MemoryMetadata.erase target=MemoryMetadata.erase source)
    (entryCell : target.locals.lookup (ofString "ent")=source.locals.lookup (ofString "ent"))
    (window : Rlp.Slices.Window source target lower upper)
    (before : pointer.toNat+length.toNat≤lower) (afterArray : upper≤array.toNat) :
    Rows target pointer length array next count items := by
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=rows.inputBefore; have upper:=array.isLt; omega
  have bytes:=Rlp.Slices.Window.bytes_before source target lower upper pointer length window before fits (MemoryMetadata.domain metadata) (MemoryMetadata.endian metadata)
  exact {rows with
    arena:=rows.arena.of_metadata metadata,entryCell:=entryCell.trans rows.entryCell
    model:=rows.model.transport source target pointer length.toNat items length.isLt bytes
    records:=rows.records.of_interval source target array pointer items (by rw [←rows.countExact]; have bound:=rows.arrayArena.upper; omega)
      (by intro query above below; exact window query (Or.inr (by omega)))
    heapCell:=by rw [globals]; exact rows.heapCell }

/-- A normally observed bounded-width store supplies its own actual writes.
The untouched input/table facts follow from record separation, including
word-tuple stores, rather than a supplied memory-preservation oracle. -/
def Rows.store_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (destination expression : ExpHOL 64) (address : BitVec 64)
    (width lower upper : Nat)
    (addressRead : eval source destination=some (.val (.word address)))
    (valueWidth : ∀ value,eval source expression=some value→(flattenHOL value).length≤width)
    (inputBefore : pointer.toNat+length.toNat≤lower) (addressLower : lower≤address.toNat)
    (addressUpper : address.toNat+8*width≤upper) (arrayAfter : upper≤array.toNat)
    (normal : evaluateHOLFiniteState source (.store destination expression)=(none,target)) :
    Rows target pointer length array next count items := by
  obtain ⟨same,memory⟩:=store_bounded_normal source target destination expression address width addressRead valueWidth normal
  have window : Rlp.Slices.Window source target lower upper:=by
    intro query outside
    apply memory query
    intro index inside equal
    have number : (address+BitVec.ofNat 64 (8*index)).toNat=address.toNat+8*index:=by
      rw [BitVec.toNat_add_of_lt (by
        have bound:=array.isLt
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
        omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have bound:=array.isLt; omega)]
    have queryNumber:=congrArg BitVec.toNat equal
    rw [number] at queryNumber
    rcases outside with before|after
    all_goals omega
  exact rows.of_window lower upper (by rw [same]; rfl) (by rw [same]) window inputBefore arrayAfter

/-- Local/clock changes with identical physical fields transport the
actual row provenance and heap while separately retaining the tuple binding. -/
def Rows.of_readonly {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items)
    (frame : LocalEffects.erase target=LocalEffects.erase source)
    (entryCell : target.locals.lookup (ofString "ent")=source.locals.lookup (ofString "ent")) : Rows target pointer length array next count items := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have metadata:=MemoryMetadata.of_frame frame
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  have bytes : ∀ offset : BitVec 64,offset.toNat<length.toNat→Rlp.ReadLength.byte source (pointer+offset)=Rlp.ReadLength.byte target (pointer+offset):=by
    intro offset inside
    exact (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>Rlp.ReadLength.byte state (pointer+offset)) frame).symm
  exact {rows with
    arena:=rows.arena.of_frame frame,entryCell:=entryCell.trans rows.entryCell
    model:=rows.model.transport source target pointer length.toNat items length.isLt bytes
    records:=by rw [memory]; exact rows.records
    heapCell:=by rw [globals]; exact rows.heapCell }

inductive Reader where | fixed | wide | word

def readerName : Reader→String | .fixed=>"tx_fixed_bytes" | .wide=>"tx_scalar_u256" | .word=>"tx_scalar_word"
def readerBody : Reader→ProgHOL 64 | .fixed=>TransactionFields.body .fixed | .wide=>TransactionNumbers.body .wide | .word=>TransactionNumbers.body .word
def readerShape : Reader→ShapeHOL | .fixed=>.one | .wide=>RlpWrite.U256Value.tupleShape | .word=>.one
def readerCap : Reader→String | .fixed=>"width" | .wide=>"maxb" | .word=>"maxb"
def readerValues (reader : Reader) (array index cap : BitVec 64) : List (ValueHOL 64):=
  [.val (.word array),.val (.word index),.val (.word cap)]++match reader with | .word=>[.val (.word 12#64)] | _=>[]
def readerArguments (reader : Reader) (index cap : BitVec 64) : List (ExpHOL 64):=
  [.rfield 0 (localVar "ent"),.const index,.const cap]++match reader with | .word=>[.const 12#64] | _=>[]
def readerOverhead : Reader→Nat | .fixed=>12 | .wide=>46 | .word=>21

theorem reader_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code)
    (reader : Reader) (array index cap : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString (readerName reader)) (readerValues reader array index cap)=some (readerBody reader,callee,readerShape reader) ∧
      callee.lookup (ofString "arr")=some (.val (.word array)) ∧ callee.lookup (ofString "i")=some (.val (.word index)) ∧
      callee.lookup (ofString (readerCap reader))=some (.val (.word cap)) := by
  cases reader with
  | fixed=>
    exact word_triple_environment source.code.lookup (ofString "tx_fixed_bytes") (ofString "arr") (ofString "i") (ofString "width")
      (TransactionFields.body .fixed) .one array index cap (by decide) (by decide) (by decide) (TransactionFields.original_code .fixed source.code installed)
  | wide=>
    exact word_triple_environment source.code.lookup (ofString "tx_scalar_u256") (ofString "arr") (ofString "i") (ofString "maxb")
      (TransactionNumbers.body .wide) RlpWrite.U256Value.tupleShape array index cap (by decide) (by decide) (by decide) (TransactionNumbers.wide_original_code source.code installed)
  | word=>
    obtain ⟨callee,called,aCell,iCell,cCell,eCell⟩:=word_quad_environment source.code.lookup (ofString "tx_scalar_word")
      (ofString "arr") (ofString "i") (ofString "maxb") (ofString "envcode") (TransactionNumbers.body .word) .one array index cap 12#64
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (TransactionNumbers.word_original_code source.code installed)
    exact ⟨callee,called,aCell,iCell,cCell⟩

theorem reader_body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length cap : BitVec 64}
    (reader : Reader) (row : TransactionNumbers.Row source array index pointer length)
    (capCell : source.locals.lookup (ofString (readerCap reader))=some (.val (.word cap))) :
    source.clock-(evaluateHOLFiniteState source (readerBody reader)).2.clock≤60*length.toNat+readerOverhead reader-1 := by
  cases reader with
  | fixed=>exact TransactionFields.body_cost source .fixed pointer length row.arena row.fits row.arguments
  | wide=>simpa [readerBody,readerOverhead,TransactionNumbers.tailPrice] using TransactionNumbers.body_cost row capCell .wide
  | word=>simpa [readerBody,readerOverhead,TransactionNumbers.tailPrice] using TransactionNumbers.body_cost row capCell .word

theorem reader_body_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array index pointer length cap : BitVec 64}
    (reader : Reader) (row : TransactionNumbers.Row source array index pointer length)
    (capCell : source.locals.lookup (ofString (readerCap reader))=some (.val (.word cap))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (readerBody reader)=(some (.returned value),target)) : Rlp.CurrentItem.Frame source target := by
  cases reader with
  | fixed=>exact TransactionFields.body_normal_frame source target .fixed pointer length row.arena row.fits row.arguments value normal
  | wide=>exact TransactionNumbers.body_normal_frame row capCell .wide value normal
  | word=>exact TransactionNumbers.body_normal_frame row capCell .word value normal

/-- Each actual nested-field call reads its genuine indexed row; its
continuation receives only the rows/frame from that same normal return. -/
theorem Rows.reader_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (reader : Reader) (index cap : BitVec 64)
    (active : index.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[index.toNat]?=some item)
    (name : String) (other : ofString "ent"≠ofString name) (continuation : ProgHOL 64) (price : Nat)
    (tail : ∀ target value,let ready:=CallNormal.continuationEntry source target name value
      Rows ready pointer length array next count items→Rlp.CurrentItem.Frame source ready→shapeEqHOL (shapeOfHOLExact value) (readerShape reader)=true→
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) (readerShape reader) (ofString (readerName reader)) (readerArguments reader index cap) continuation)).2.clock≤60*item.size+readerOverhead reader+price := by
  obtain ⟨callee,called,aCell,iCell,cCell⟩:=reader_environment source rows.arena.code reader array index cap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (readerArguments reader index cap)=some (readerValues reader array index cap):=by
    cases reader <;> simp [readerArguments,readerValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
  have row:=rows.row index active item selected callee aCell iCell
  have bodyPrice:=reader_body_cost reader row cCell
  have actual:=ClockCost.scoped_reached_current source name (readerShape reader) (ofString (readerName reader)) (readerArguments reader index cap) _ (readerBody reader) continuation callee (readerShape reader)
    (60*item.total.toNat+readerOverhead reader-1) price args called bodyPrice (by
      intro target value normal checked
      have frame:=reader_body_frame reader row cCell value normal
      have callerFrame : Rlp.CurrentItem.Frame source target:=frame.of_erase rfl rfl
      exact tail target value (rows.reader_resume name value other callerFrame) (callerFrame.of_erase rfl rfl) (by simpa only [Bool.and_self] using checked))
  have size:=(rows.model.at_span source pointer length.toNat items index.toNat item selected (by
    have before:=rows.inputBefore; have upper:=array.isLt; omega)).1
  rw [size] at actual
  cases reader <;> simp only [readerOverhead] at actual ⊢ <;> omega

/-- A real assigned reader return supplies the same actual rows, shape
and physical frame as a scoped reader, with the saved caller binding updated. -/
theorem Rows.assigned_reader_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (reader : Reader) (index cap : BitVec 64)
    (active : index.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[index.toNat]?=some item)
    (name : String) (other : ofString "ent"≠ofString name)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) (readerArguments reader index cap))=(none,target)) :
    ∃ child value,target=CallNormal.continuationEntry source child name value ∧
      Rows target pointer length array next count items ∧ Rlp.CurrentItem.Frame source target ∧ shapeEqHOL (shapeOfHOLExact value) (readerShape reader)=true := by
  obtain ⟨callee,called,aCell,iCell,cCell⟩:=reader_environment source rows.arena.code reader array index cap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (readerArguments reader index cap)=some (readerValues reader array index cap):=by
    cases reader <;> simp [readerArguments,readerValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
  obtain ⟨funded,values,body,actual,shape,child,value,argsRead,lookup,bodyRun,checked,endpoint⟩:=CallNormal.local_data source target (ofString name) _ _ normal
  have valueEq:=Option.some.inj (argsRead.symm.trans args)
  subst values
  have same:=Option.some.inj (lookup.symm.trans called)
  have bodyEq:=congrArg Prod.fst same
  have actualEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
  change body=readerBody reader at bodyEq
  change actual=callee at actualEq
  change shape=readerShape reader at shapeEq
  subst body actual shape
  have frame:=reader_body_frame reader (rows.row index active item selected callee aCell iCell) cCell value bodyRun
  have callerFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
  have resumed:=rows.reader_resume name value other callerFrame
  refine ⟨child,value,endpoint,?_,?_,checked⟩
  · rw [endpoint]; exact resumed
  · exact callerFrame.of_erase rfl (by rw [endpoint]; rfl)

/-- Actual assigned numeric/fixed-reader call and its genuine resumed
suffix, including every stopped call/assignment outcome. -/
theorem Rows.assigned_reader_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (reader : Reader) (index cap : BitVec 64)
    (active : index.toNat<count.toNat) (item : Rlp.ListItem) (selected : items[index.toNat]?=some item)
    (name : String) (other : ofString "ent"≠ofString name) (continuation : ProgHOL 64) (price : Nat)
    (tail : ∀ child value,let ready:=CallNormal.continuationEntry source child name value
      Rows ready pointer length array next count items→Rlp.CurrentItem.Frame source ready→shapeEqHOL (shapeOfHOLExact value) (readerShape reader)=true→
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.seq (.call (some (some (.local,ofString name),none)) (ofString (readerName reader)) (readerArguments reader index cap)) continuation)).2.clock≤60*item.size+readerOverhead reader+price := by
  obtain ⟨callee,called,aCell,iCell,cCell⟩:=reader_environment source rows.arena.code reader array index cap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (readerArguments reader index cap)=some (readerValues reader array index cap):=by
    cases reader <;> simp [readerArguments,readerValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
  have row:=rows.row index active item selected callee aCell iCell
  have bodyPrice:=reader_body_cost reader row cCell
  have callerPrice:=ClockCost.assigned_current source (some (.local,ofString name)) _ _ _ (readerBody reader) callee (readerShape reader)
    (60*item.total.toNat+readerOverhead reader-1) args called bodyPrice
  have actual:=ClockCost.sequence_reached_current source _ continuation ((60*item.total.toNat+readerOverhead reader-1)+1) price callerPrice (by
    intro target normal
    obtain ⟨child,value,endpoint,resumed,frame,checked⟩:=rows.assigned_reader_normal reader index cap active item selected name other normal
    rw [endpoint] at resumed frame ⊢
    exact tail child value resumed frame checked)
  have size:=(rows.model.at_span source pointer length.toNat items index.toNat item selected (by have before:=rows.inputBefore; have upper:=array.isLt; omega)).1
  rw [size] at actual
  cases reader <;> simp only [readerOverhead] at actual ⊢ <;> omega

/-- A real normally continuing guard/sequence proves the guard passed
at exactly its incoming state and supplies the actual remaining run. -/
theorem guard_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : ProgHOL 64)
    (guard : PureGuard first) (normal : evaluateHOLFiniteState source (.seq first second)=(none,target)) :
    evaluateHOLFiniteState source first=(none,source) ∧ evaluateHOLFiniteState source second=(none,target) := by
  obtain ⟨middle,front,back⟩:=sequence_none source target first second normal
  have same:=(guard.summary source).1 (congrArg Prod.fst front)
  rw [front] at same
  change middle=source at same
  subst middle
  exact ⟨front,back⟩

theorem restore_key (saved state : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (key : MlS)
    (other : key≠ofString name) : (restore saved name state).locals.lookup key=state.locals.lookup key := by
  change (HolFiniteMapExact.resVarEq state.locals (ofString name,saved.locals.lookup (ofString name))).lookup key=_
  rw [lookup_resVarEq_toExact]
  cases saved.locals.lookup (ofString name) <;> simp [resVarHOLExact,FUPDATE,FDOMSUB,other]

theorem restore_key_same (saved state : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) :
    (restore saved name state).locals.lookup (ofString name)=saved.locals.lookup (ofString name) := by
  change (HolFiniteMapExact.resVarEq state.locals (ofString name,saved.locals.lookup (ofString name))).lookup (ofString name)=_
  rw [lookup_resVarEq_toExact]
  cases saved.locals.lookup (ofString name) <;> simp [resVarHOLExact,FUPDATE,FDOMSUB]

/-- Invert the same actually continuing nested iteration. Its real parser,
conversion and arity guards expose the genuine field state and remaining run,
including saved caller bindings and physical scope restoration. -/
theorem iteration_prefix_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (kind : Kind) (entry : Entry source pointer length heap)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length))
    (normal : evaluateHOLFiniteState source (iteration kind)=(none,target)) :
    ∃ current inner payloadPointer payloadLength next count items,
      payloadPointer.toNat+payloadLength.toNat≤pointer.toNat+length.toNat ∧ payloadLength.toNat≤length.toNat ∧
      Rows current payloadPointer payloadLength heap next count items ∧ count=expected kind ∧
      PersistentNormalFrame source current heap ∧
      (∀ key,key≠ofString "it"→key≠ofString "ent"→current.locals.lookup key=source.locals.lookup key) ∧
      evaluateHOLFiniteState current (fields kind)=(none,inner) ∧
      LocalEffects.erase target=LocalEffects.erase inner ∧
      (∀ key,key≠ofString "it"→key≠ofString "ent"→target.locals.lookup key=inner.locals.lookup key) ∧
      (∀ key,key=ofString "it" ∨ key=ofString "ent"→target.locals.lookup key=source.locals.lookup key) ∧
      pointer.toNat≤payloadPointer.toNat := by
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=entry.inputBefore; have bound:=heap.isLt; omega
  obtain ⟨itemCallee,itemCall,pointerCell,lengthCell⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape pointer length
    (Rlp.Item.original_code source.code entry.arena.code)
  rw [(shapes kind).1] at normal
  obtain ⟨funded,itemPost,value,afterIt,itemRun,itemChecked,afterItemRun,itemEndpoint⟩:=CallNormal.scoped_none source target "it" Rlp.Item.resultShape (ofString "rlp_item") rowArguments _ Rlp.Item.body (afterItem kind) itemCallee Rlp.Item.resultShape args itemCall normal
  obtain ⟨valid,itemFrame,itemPrice⟩:=Rlp.CurrentItem.body_normal (callEntryStateHOLFinite source itemCallee) itemPost pointer length pointerCell lengthCell
    (entry.arena.of_frame rfl) fits entry.arena.code value itemRun
  have callerFrame : Rlp.CurrentItem.Frame source itemPost:=itemFrame.of_erase rfl rfl
  obtain ⟨header,payload,flag,answer,small,positive,bounded,binary,listHeader⟩:=valid
  let ready:=CallNormal.continuationEntry source itemPost "it" value
  have runtime : MemoryMetadata.erase ready=MemoryMetadata.erase source:=callerFrame.metadata
  have globals:=congrArg PanSemStateFiniteExact.globals runtime
  change ready.globals=source.globals at globals
  have payloadNumber : (pointer+header).toNat=pointer.toNat+header.toNat:=by rw [BitVec.toNat_add_of_lt (by omega)]
  have contained : (pointer+header).toNat+payload.toNat≤pointer.toNat+length.toNat:=by rw [payloadNumber]; omega
  have payloadBound : payload.toNat≤length.toNat:=by omega
  have nextEntry : Entry ready (pointer+header) payload heap:=⟨entry.arena.of_metadata runtime,
    by rw [globals]; exact entry.heapCell,entry.heapArena,entry.heapBound,entry.heapAligned,by have before:=entry.inputBefore; omega⟩
  have parseFrame:=(PersistentNormalFrame.refl source heap entry.heapCell entry.heapArena entry.heapBound entry.heapAligned).after_memory source source ready heap runtime (by
    intro query before; exact callerFrame.outside query (Or.inl (by have upper:=entry.heapBound; omega)))
  have payloadArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) payloadArguments=some (Rlp.Header.values (pointer+header) payload):=by
    simp [ready,CallNormal.continuationEntry,payloadArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer,Rlp.Item.result]
  rw [(shapes kind).2.1] at afterItemRun
  obtain ⟨tagPassed,conversionRun⟩:=guard_none ready afterIt (itemGuard kind) _ (.ite _ (.raise _ _) .skip) afterItemRun
  obtain ⟨sliceCallee,sliceCall,pCell,nCell⟩:=Rlp.environment ready.code.lookup (ofString "rlp_list_to_slices") Rlp.Slices.body Rlp.Slices.resultShape (pointer+header) payload
    (Rlp.Slices.original_code ready.code nextEntry.arena.code)
  obtain ⟨fundedSlices,slicePost,sliceValue,inner,sliceRun,sliceChecked,countRun,sliceEndpoint⟩:=CallNormal.scoped_none ready afterIt "ent" Rlp.Slices.resultShape (ofString "rlp_list_to_slices") payloadArguments _ Rlp.Slices.body (afterConversion kind) sliceCallee Rlp.Slices.resultShape payloadArgs sliceCall conversionRun
  obtain ⟨items,count,model,countExact,countBound,sliceAnswer,records,room,arena,sliceGlobals,window,metadata,above,spent⟩:=Rlp.CurrentSlices.body_normal
    (callEntryStateHOLFinite ready sliceCallee) slicePost (pointer+header) payload heap pCell nCell (nextEntry.arena.of_frame rfl) nextEntry.heapCell nextEntry.heapBound nextEntry.inputBefore
      (by have before:=nextEntry.inputBefore; have bound:=nextEntry.heapBound; omega) sliceValue sliceRun
  rw [sliceAnswer] at countRun
  let current:=CallNormal.continuationEntry ready slicePost "ent" (Rlp.Slices.result heap count)
  have rows:=rows_from_converter nextEntry model countExact countBound records room arena sliceGlobals
  have converted:=Rlp.CurrentSlices.persistent_frame_of_return ready slicePost heap count entry.heapArena room metadata window
  have currentFrame:=converted.of_erase ready slicePost ready current heap rfl rfl
  have totalFrame:=parseFrame.trans source ready current heap heap currentFrame (Nat.le_refl _)
  rw [(shapes kind).2.2] at countRun
  obtain ⟨countPassed,fieldRun⟩:=guard_none current inner (countGuard kind) (fields kind) (.ite _ (.raise _ _) .skip) countRun
  have countRead : eval current (.rfield 1 (localVar "ent"))=some (.val (.word count)):=by
    simp [current,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,eval,evalHOLExact,toExact,localVar,Rlp.Slices.result]
  have arity:=TransactionFields.reject_unequal_normal current current (.rfield 1 (localVar "ent")) (.const (expected kind)) (errorCode kind) count (expected kind) countRead rfl countPassed
  refine ⟨current,inner,pointer+header,payload,_,count,items,contained,payloadBound,rows,arity,totalFrame,?_,fieldRun,?_,?_,?_,?_⟩
  · intro key notIt notEnt
    simp [current,ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notIt,notEnt,Ne.symm notIt,Ne.symm notEnt]
  · rw [itemEndpoint,sliceEndpoint]; rfl
  · intro key notIt notEnt
    rw [itemEndpoint,sliceEndpoint]
    exact (restore_key source _ "it" key notIt).trans (restore_key ready inner "ent" key notEnt)

  · intro key which
    rcases which with rfl|rfl
    · rw [itemEndpoint]
      exact restore_key_same source afterIt "it"
    · rw [itemEndpoint,sliceEndpoint]
      have first:=restore_key source (restore ready "ent" inner) "it" (ofString "ent") (by decide)
      have second:=restore_key_same ready inner "ent"
      have original : ready.locals.lookup (ofString "ent")=source.locals.lookup (ofString "ent"):=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
          show ofString "it"≠ofString "ent" from by decide]
      exact first.trans (second.trans original)

  · rw [payloadNumber]; omega

/-- The selected stored row is genuinely contained in the original
converted payload, with its exact nonwrapping encoded byte extent. -/
theorem Rows.item_span {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) :
    item.total.toNat=item.size ∧ (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat≤pointer.toNat+length.toNat := by
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=rows.inputBefore; have bound:=array.isLt; omega
  have span:=rows.model.at_span source pointer length.toNat items index item selected fits
  obtain ⟨offset,path,bounded,valid,encoded⟩:=rows.model.at source pointer length.toNat items index item selected
  have number : (Rlp.Slices.itemPointer pointer items index).toNat=pointer.toNat+offset:=by
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact ⟨span.1,by rw [number,span.1]; omega⟩

/-- A same-return reader frame supplies a real persistent frame at the
current observed heap, including its unchanged nonheap globals. -/
theorem Rows.reader_persistent {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next count : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next count items) (frame : Rlp.CurrentItem.Frame source target) : PersistentNormalFrame source target next := by
  have initial:=PersistentNormalFrame.refl source next rows.heapCell rows.heapArena rows.heapBound rows.heapAligned
  exact initial.after_memory source source target next frame.metadata (by
    intro query before; exact frame.outside query (Or.inl (by have bound:=rows.heapBound; omega)))

end InitECandidate.Solver.Input.CurrentVerify.NestedLists

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.rows_from_converter
#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.after_conversion_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.conversion_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.iteration_prefix_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.row

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.reader_resume

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.reader_environment

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.reader_body_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.reader_body_frame

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.reader_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.of_window

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.store_resume

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.assigned_reader_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.assigned_reader_cost

namespace InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch NestedLists

def reader : Nat→Reader | 1=>.fixed | 2=>.word | 3=>.word | _=>.wide
def fieldName : Nat→String | 0=>"cid" | 1=>"addr" | 2=>"w" | 3=>"w" | 4=>"r" | _=>"s"
def cap : Nat→BitVec 64 | 1=>20#64 | 2=>8#64 | 3=>1#64 | _=>32#64
def offset : Nat→Nat | 0=>0 | 1=>32 | 2=>40 | 3=>48 | 4=>56 | _=>88
def width : Reader→Nat | .wide=>4 | _=>1

def destination (phase : Nat) : ExpHOL 64:=.op .add [localVar "a",.const (BitVec.ofNat 64 (offset phase))]
def store (phase : Nat) : ProgHOL 64:=.store (destination phase) (localVar (fieldName phase))
def increment : ProgHOL 64:=.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def program : List Nat→ProgHOL 64
  | []=>increment
  | phase::rest=>
    let suffix:=.seq (store phase) (program rest)
    if phase=3 then
      .seq (.call (some (some (.local,ofString (fieldName phase)),none)) (ofString (readerName (reader phase))) (readerArguments (reader phase) (BitVec.ofNat 64 phase) (cap phase))) suffix
    else .decCall (ofString (fieldName phase)) (readerShape (reader phase)) (ofString (readerName (reader phase))) (readerArguments (reader phase) (BitVec.ofNat 64 phase) (cap phase)) suffix

def recordExpression : ExpHOL 64:=.op .add [localVar "recs",.panop .mul [localVar "i",.const 120#64]]

set_option maxRecDepth 100000 in
/-- Literal syntax of all six actual field calls/stores, including the
assigned fourth call and the final outer-index increment. -/
theorem fields_shape : NestedLists.fields .authorization=.dec (ofString "a") .one recordExpression (program [0,1,2,3,4,5]) := by
  simp only [NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    Guest.Software.guestFn_decode_authorizations,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,
    program,reader,fieldName,cap,offset,destination,store,increment,recordExpression,readerShape,readerName,readerArguments,localVar,
    RlpWrite.U256Value.tupleShape,if_pos rfl,show (0:Nat)≠3 from by decide,show (1:Nat)≠3 from by decide,
    show (2:Nat)≠3 from by decide,show (4:Nat)≠3 from by decide,show (5:Nat)≠3 from by decide]
  rfl

structure State (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array next record : BitVec 64) (items : List Rlp.ListItem) where
  rows : Rows source pointer length array next 6#64 items
  recordCell : source.locals.lookup (ofString "a")=some (.val (.word record))
  inputBefore : pointer.toNat+length.toNat≤record.toNat
  recordBefore : record.toNat+120≤array.toNat

/-- Actual reader calls restore the original record binding and retain
both separated live inputs; numeric values are not assumed in advance. -/
def State.reader_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (data : State source pointer length array next record items) (phase : Nat) (value : ValueHOL 64)
    (frame : Rlp.CurrentItem.Frame source target) :
    State (CallNormal.continuationEntry source target (fieldName phase) value) pointer length array next record items := by
  have notEnt : ofString "ent"≠ofString (fieldName phase):=by
    unfold fieldName; split <;> decide
  have notA : ofString (fieldName phase)≠ofString "a":=by
    unfold fieldName; split <;> decide
  exact ⟨data.rows.reader_resume (fieldName phase) value notEnt frame,
    by simpa [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notA] using data.recordCell,
    data.inputBefore,data.recordBefore⟩

/-- The real checked scalar/four-word return shape bounds the flattened
record write without requiring numeric value semantics. -/
theorem value_width (kind : Reader) (value : ValueHOL 64)
    (checked : shapeEqHOL (shapeOfHOLExact value) (readerShape kind)=true) : (flattenHOL value).length=width kind := by
  have shape:=(shapeEqHOL_eq_true _ _).mp checked
  cases kind with
  | fixed=>
    obtain ⟨word,rfl⟩:=RlpWrite.U256Value.scalar_word value shape
    simp [flattenHOL,width]
  | word=>
    obtain ⟨word,rfl⟩:=RlpWrite.U256Value.scalar_word value shape
    simp [flattenHOL,width]
  | wide=>
    obtain ⟨words,rfl⟩:=RlpWrite.U256Value.of_shape value shape
    simp [RlpWrite.U256Value.tuple,flattenHOL,width]

theorem phase_room (phase : Nat) (inside : phase<6) : offset phase+8*width (reader phase)≤120 := by
  have cases : phase=0 ∨ phase=1 ∨ phase=2 ∨ phase=3 ∨ phase=4 ∨ phase=5:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Only the same observed typed reader result is written. A genuine
normal store retains the input/table/record model for the next field. -/
def State.store_resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (data : State source pointer length array next record items) (phase : Nat) (inside : phase<6) (value : ValueHOL 64)
    (cell : source.locals.lookup (ofString (fieldName phase))=some value)
    (checked : shapeEqHOL (shapeOfHOLExact value) (readerShape (reader phase))=true)
    (normal : evaluateHOLFiniteState source (store phase)=(none,target)) : State target pointer length array next record items := by
  have room:=phase_room phase inside
  have bound:=array.isLt
  have recordBefore:=data.recordBefore
  have number : (record+BitVec.ofNat 64 (offset phase)).toNat=record.toNat+offset phase:=by
    rw [BitVec.toNat_add_of_lt (by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have read : eval source (destination phase)=some (.val (.word (record+BitVec.ofNat 64 (offset phase)))):=by
    simp [destination,eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.recordCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have actualValue : ∀ actual,eval source (localVar (fieldName phase))=some actual→(flattenHOL actual).length≤width (reader phase):=by
    intro actual observed
    have same : value=actual:=by simpa [eval,evalHOLExact,toExact,localVar,cell] using observed
    subst actual
    exact Nat.le_of_eq (value_width (reader phase) value checked)
  have nextRows:=data.rows.store_resume (destination phase) (localVar (fieldName phase)) (record+BitVec.ofNat 64 (offset phase))
    (width (reader phase)) record.toNat (record.toNat+120) read actualValue data.inputBefore (by rw [number]; omega) (by rw [number]; omega) data.recordBefore normal
  have fields:=store_none_frame source target (destination phase) (localVar (fieldName phase)) normal
  exact ⟨nextRows,by rw [fields]; exact data.recordCell,data.inputBefore,data.recordBefore⟩

def rowBytes (items : List Rlp.ListItem) (phase : Nat) : Nat:=((items[phase]?).map Rlp.ListItem.size).getD 0
def charge (items : List Rlp.ListItem) : List Nat→Nat
  | []=>0
  | phase::rest=>60*rowBytes items phase+readerOverhead (reader phase)+charge items rest

/-- All six real field operations: a selected row pays for its actual
reader and the following record store; every early stop is included. -/
theorem program_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (data : State source pointer length array next record items) (phases : List Nat) (inside : ∀ phase∈phases,phase<6) :
    source.clock-(evaluateHOLFiniteState source (program phases)).2.clock≤charge items phases := by
  induction phases generalizing source with
  | nil=>exact ClockCost.assign source.code _ _ source rfl
  | cons phase rest ih=>
    have phaseInside:=inside phase (by simp)
    have restInside : ∀ index∈rest,index<6:=by intro index member; exact inside index (by simp [member])
    have size:=data.rows.countExact
    change 6=items.length at size
    have selected : ∃ item,items[phase]?=some item:=⟨items[phase]'(by omega),List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩⟩
    obtain ⟨item,selected⟩:=selected
    have indexNumber : (BitVec.ofNat 64 phase).toNat=phase:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have active : (BitVec.ofNat 64 phase).toNat<(6#64 : BitVec 64).toNat:=by rw [indexNumber]; exact phaseInside
    have indexed : items[(BitVec.ofNat 64 phase).toNat]?=some item:=by rw [indexNumber]; exact selected
    have other : ofString "ent"≠ofString (fieldName phase):=by unfold fieldName; split <;> decide
    have suffix : ∀ target value,
        Rows (CallNormal.continuationEntry source target (fieldName phase) value) pointer length array next 6#64 items→
        Rlp.CurrentItem.Frame source (CallNormal.continuationEntry source target (fieldName phase) value)→
        shapeEqHOL (shapeOfHOLExact value) (readerShape (reader phase))=true→
        (CallNormal.continuationEntry source target (fieldName phase) value).clock-
          (evaluateHOLFiniteState (CallNormal.continuationEntry source target (fieldName phase) value) (.seq (store phase) (program rest))).2.clock≤charge items rest:=by
      intro target value rows frame checked
      let ready:=CallNormal.continuationEntry source target (fieldName phase) value
      have actualFrame : Rlp.CurrentItem.Frame source target:=frame.of_erase rfl rfl
      have nextData:=data.reader_resume phase value actualFrame
      have cell : ready.locals.lookup (ofString (fieldName phase))=some value:=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      have all:=ClockCost.sequence_reached_current ready (store phase) (program rest) 0 (charge items rest)
        (ClockCost.store ready.code _ _ ready rfl) (by
          intro middle normal
          exact ih (nextData.store_resume phase phaseInside value cell checked normal) restInside)
      simpa only [Nat.zero_add] using all
    have price : source.clock-(evaluateHOLFiniteState source (program (phase::rest))).2.clock≤60*item.size+readerOverhead (reader phase)+charge items rest:=by
      rw [program]
      split
      · exact data.rows.assigned_reader_cost (reader phase) (BitVec.ofNat 64 phase) (cap phase) active item indexed (fieldName phase) other _ (charge items rest) suffix
      · exact data.rows.reader_cost (reader phase) (BitVec.ofNat 64 phase) (cap phase) active item indexed (fieldName phase) other _ (charge items rest) suffix
    simpa only [charge,rowBytes,selected,Option.map_some,Option.getD_some] using price

/-- Every actual authorization field appears once. Its parsed byte extent
is charged once, with192 constant caller/conversion ticks in total. -/
theorem charge_six (items : List Rlp.ListItem) (length : Nat) (count : items.length=6)
    (bytes : (items.map Rlp.ListItem.size).sum=length) : charge items [0,1,2,3,4,5]=60*length+192 := by
  cases items with
  | nil=>simp at count
  | cons a0 items=>
    cases items with
    | nil=>simp at count
    | cons a1 items=>
      cases items with
      | nil=>simp at count
      | cons a2 items=>
        cases items with
        | nil=>simp at count
        | cons a3 items=>
          cases items with
          | nil=>simp at count
          | cons a4 items=>
            cases items with
            | nil=>simp at count
            | cons a5 rest=>
              have empty : rest=[]:=by
                cases rest with
                | nil=>rfl
                | cons head tail=>simp only [List.length_cons] at count; omega
              subst rest
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at bytes
              simp [charge,rowBytes,reader,readerOverhead]
              omega

/-- Complete actual authorization field suffix from its real record-address
read and checked six-row table. No future field/store success is assumed. -/
theorem fields_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next 6#64 items)
    (read : eval source recordExpression=some (.val (.word record)))
    (inputBefore : pointer.toNat+length.toNat≤record.toNat) (recordBefore : record.toNat+120≤array.toNat) :
    source.clock-(evaluateHOLFiniteState source (NestedLists.fields .authorization)).2.clock≤60*length.toNat+192 := by
  rw [fields_shape]
  let ready:=QueryBranch.bind source "a" record
  have data : State ready pointer length array next record items:=⟨rows.reader_resume "a" (.val (.word record)) (by decide) (.of_readonly rfl),bind_lookup_same _ _ _,inputBefore,recordBefore⟩
  have actual:=program_cost data [0,1,2,3,4,5] (by intro phase member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega)
  have count:=rows.countExact
  change 6=items.length at count
  rw [charge_six items length.toNat count.symm (rows.model.total_size source pointer length.toNat items)] at actual
  exact ClockCost.declared_current source "a" recordExpression record (program [0,1,2,3,4,5]) (60*length.toNat+192) read actual

/-- Scope restoration changes only the saved field binding, which is
distinct from the live tuple and record-address bindings. -/
def State.restored {inner : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (data : State inner pointer length array next record items) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (phase : Nat) :
    State (restore source (fieldName phase) inner) pointer length array next record items := by
  have notEnt : ofString "ent"≠ofString (fieldName phase):=by unfold fieldName; split <;> decide
  have notA : ofString "a"≠ofString (fieldName phase):=by unfold fieldName; split <;> decide
  exact ⟨data.rows.of_readonly rfl (restore_lookup_other source inner (fieldName phase) "ent" notEnt),
    (restore_lookup_other source inner (fieldName phase) "a" notA).trans data.recordCell,data.inputBefore,data.recordBefore⟩

/-- A normal field store changes memory alone and cannot write before its
actual record. The flattened width comes from the same checked reader value. -/
theorem State.store_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (data : State source pointer length array next record items) (phase : Nat) (inside : phase<6) (value : ValueHOL 64)
    (cell : source.locals.lookup (ofString (fieldName phase))=some value)
    (checked : shapeEqHOL (shapeOfHOLExact value) (readerShape (reader phase))=true)
    (normal : evaluateHOLFiniteState source (store phase)=(none,target)) :
    MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<record.toNat→target.memory query=source.memory query := by
  have room:=phase_room phase inside
  have bound:=array.isLt
  have recordBefore:=data.recordBefore
  have read : eval source (destination phase)=some (.val (.word (record+BitVec.ofNat 64 (offset phase)))):=by
    simp [destination,eval,evalHOLExact,evalListHOLExact,toExact,localVar,data.recordCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have actualValue : ∀ actual,eval source (localVar (fieldName phase))=some actual→(flattenHOL actual).length≤width (reader phase):=by
    intro actual observed
    have same : value=actual:=by simpa [eval,evalHOLExact,toExact,localVar,cell] using observed
    subst actual
    exact Nat.le_of_eq (value_width (reader phase) value checked)
  obtain ⟨same,memory⟩:=store_bounded_normal source target (destination phase) (localVar (fieldName phase))
    (record+BitVec.ofNat 64 (offset phase)) (width (reader phase)) read actualValue normal
  refine ⟨by rw [same]; rfl,?_⟩
  intro query before
  apply memory query
  intro index indexed equal
  have number : (record+BitVec.ofNat 64 (offset phase)+BitVec.ofNat 64 (8*index)).toNat=record.toNat+offset phase+8*index:=by
    rw [BitVec.add_assoc,←BitVec.ofNat_add,BitVec.toNat_add_of_lt (by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have queryNumber:=congrArg BitVec.toNat equal
  rw [number] at queryNumber
  omega

/-- Genuine normal completion of the field chain retains its live table,
metadata and every earlier word, for both scoped and assigned reader calls. -/
theorem program_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (data : State source pointer length array next record items) (phases : List Nat) (inside : ∀ phase∈phases,phase<6)
    (normal : evaluateHOLFiniteState source (program phases)=(none,target)) :
    ∃ final : State target pointer length array next record items,
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<record.toNat→target.memory query=source.memory query := by
  induction phases generalizing source target with
  | nil=>
    have frame:=LocalEffects.assign source.code (ofString "i") (.op .add [localVar "i",.const 1#64]) source rfl
    change LocalEffects.erase (evaluateHOLFiniteState source (program [])).2=LocalEffects.erase source at frame
    rw [normal] at frame
    have entSame:=((LocalPrefix.assign (key:=ofString "ent") (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide)).summary_full source).1
    have aSame:=((LocalPrefix.assign (key:=ofString "a") (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide)).summary_full source).1
    change (evaluateHOLFiniteState source (program [])).1=none→(evaluateHOLFiniteState source (program [])).2.locals.lookup (ofString "ent")=source.locals.lookup (ofString "ent") at entSame
    change (evaluateHOLFiniteState source (program [])).1=none→(evaluateHOLFiniteState source (program [])).2.locals.lookup (ofString "a")=source.locals.lookup (ofString "a") at aSame
    rw [normal] at entSame aSame
    exact ⟨⟨data.rows.of_readonly frame (entSame rfl),(aSame rfl).trans data.recordCell,data.inputBefore,data.recordBefore⟩,
      MemoryMetadata.of_frame frame,by intro query before; exact congrFun (LocalEffects.memory_of_erase source target frame) query⟩
  | cons phase rest ih=>
    have phaseInside:=inside phase (by simp)
    have restInside : ∀ index∈rest,index<6:=by intro index member; exact inside index (by simp [member])
    have size:=data.rows.countExact
    change 6=items.length at size
    obtain ⟨item,selected⟩ : ∃ item,items[phase]?=some item:=⟨items[phase]'(by omega),List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩⟩
    have indexNumber : (BitVec.ofNat 64 phase).toNat=phase:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have active : (BitVec.ofNat 64 phase).toNat<(6#64 : BitVec 64).toNat:=by rw [indexNumber]; exact phaseInside
    have indexed : items[(BitVec.ofNat 64 phase).toNat]?=some item:=by rw [indexNumber]; exact selected
    have other : ofString "ent"≠ofString (fieldName phase):=by unfold fieldName; split <;> decide
    have suffix : ∀ child value inner,
        Rlp.CurrentItem.Frame source child→shapeEqHOL (shapeOfHOLExact value) (readerShape (reader phase))=true→
        evaluateHOLFiniteState (CallNormal.continuationEntry source child (fieldName phase) value) (.seq (store phase) (program rest))=(none,inner)→
        ∃ final : State inner pointer length array next record items,
          MemoryMetadata.erase inner=MemoryMetadata.erase source ∧
          ∀ query : BitVec 64,query.toNat<record.toNat→inner.memory query=source.memory query:=by
      intro child value inner frame checked continued
      let ready:=CallNormal.continuationEntry source child (fieldName phase) value
      have readyData:=data.reader_resume phase value frame
      have cell : ready.locals.lookup (ofString (fieldName phase))=some value:=by
        simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      obtain ⟨stored,storeRun,restRun⟩:=sequence_none ready inner (store phase) (program rest) continued
      have storedData:=readyData.store_resume phase phaseInside value cell checked storeRun
      obtain ⟨storeMetadata,storeMemory⟩:=readyData.store_frame phase phaseInside value cell checked storeRun
      obtain ⟨final,metadata,memory⟩:=ih storedData restInside restRun
      exact ⟨final,metadata.trans (storeMetadata.trans frame.metadata),by
        intro query before
        exact (memory query before).trans ((storeMemory query before).trans (frame.outside query (Or.inl (by
          have recordBefore:=data.recordBefore; have arrayBefore:=data.rows.arrayBefore; have heapBound:=data.rows.heapBound; omega))))⟩
    rw [program] at normal
    split at normal
    · obtain ⟨returned,callRun,suffixRun⟩:=sequence_none source target _ _ normal
      obtain ⟨child,value,endpoint,rows,frame,checked⟩:=data.rows.assigned_reader_normal (reader phase) (BitVec.ofNat 64 phase) (cap phase) active item indexed (fieldName phase) other callRun
      rw [endpoint] at suffixRun frame
      have childFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
      exact suffix child value target childFrame checked suffixRun
    · obtain ⟨callee,called,aCell,iCell,cCell⟩:=reader_environment source data.rows.arena.code (reader phase) array (BitVec.ofNat 64 phase) (cap phase)
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (readerArguments (reader phase) (BitVec.ofNat 64 phase) (cap phase))=some (readerValues (reader phase) array (BitVec.ofNat 64 phase) (cap phase)):=by
        cases reader phase <;> simp [readerArguments,readerValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.rows.entryCell,Rlp.Slices.result]
      obtain ⟨funded,child,value,inner,bodyRun,checked,suffixRun,endpoint⟩:=CallNormal.scoped_none source target (fieldName phase) (readerShape (reader phase)) (ofString (readerName (reader phase)))
        (readerArguments (reader phase) (BitVec.ofNat 64 phase) (cap phase)) _ (readerBody (reader phase)) _ callee (readerShape (reader phase)) args called normal
      have frame:=reader_body_frame (reader phase) (data.rows.row _ active item indexed callee aCell iCell) cCell value bodyRun
      have childFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
      obtain ⟨final,metadata,memory⟩:=suffix child value inner childFrame (by simpa only [Bool.and_self] using checked) suffixRun
      refine ⟨?_,?_,?_⟩
      · rw [endpoint]; exact final.restored source phase
      · rw [endpoint]; exact metadata
      · intro query before; rw [endpoint]; exact memory query before

/-- Each genuinely continuing field chain advances the outer transaction
entry index exactly once, regardless of helper-local counter names. -/
theorem program_advance (phases : List Nat) : CounterFlow.Advances (ofString "i") 1 (program phases) := by
  induction phases with
  | nil=>simpa only [program,increment,localVar] using CounterFlow.increment (ofString "i")
  | cons phase rest ih=>
    have other : ofString "i"≠ofString (fieldName phase):=by unfold fieldName; split <;> decide
    have stored : CounterFlow.Advances (ofString "i") 1 (.seq (store phase) (program rest)):=by
      simpa only [Nat.zero_add,store] using CounterFlow.sequence (ofString "i") _ _ 0 1
        (CounterFlow.preserved _ _ (.store _ _)) ih
    rw [program]
    split
    · simpa only [Nat.zero_add,Option.map_some] using CounterFlow.sequence (ofString "i") _ _ 0 1
        (CounterFlow.preserved _ _ (.call (some (ofString (fieldName phase))) _ _ (by intro name equal; cases equal; exact other))) stored
    · exact CounterFlow.scoped_call (ofString "i") (fieldName phase) _ _ _ _ 1 other stored

/-- The actual record-address scope preserves normal physical effects and
all earlier input, and advances the genuine enclosing loop index once. -/
theorem fields_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next record : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next 6#64 items)
    (read : eval source recordExpression=some (.val (.word record)))
    (inputBefore : pointer.toNat+length.toNat≤record.toNat) (recordBefore : record.toNat+120≤array.toNat)
    (normal : evaluateHOLFiniteState source (NestedLists.fields .authorization)=(none,target)) :
    MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<record.toNat→target.memory query=source.memory query := by
  rw [fields_shape] at normal
  obtain ⟨inner,continued,endpoint⟩:=declaration_none_word source target "a" recordExpression record (program [0,1,2,3,4,5]) read normal
  let ready:=QueryBranch.bind source "a" record
  have data : State ready pointer length array next record items:=⟨rows.reader_resume "a" (.val (.word record)) (by decide) (.of_readonly rfl),bind_lookup_same _ _ _,inputBefore,recordBefore⟩
  obtain ⟨final,metadata,memory⟩:=program_normal data [0,1,2,3,4,5] (by intro phase member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member; omega) continued
  exact ⟨by rw [endpoint]; exact metadata,by intro query before; rw [endpoint]; exact memory query before⟩

theorem fields_advance : CounterFlow.Advances (ofString "i") 1 (NestedLists.fields .authorization) := by
  rw [fields_shape]
  exact CounterFlow.declared (ofString "i") (ofString "a") .one recordExpression _ 1 (by decide) (program_advance _)

/-- Complete actual authorization iteration from its selected outer row
and previously allocated record slot. Its own parser/converter/arity guard
supply every six-field entry condition; stopped outcomes are all included. -/
theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap records index : BitVec 64}
    (entry : NestedLists.Entry source pointer length heap)
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (inputBefore : pointer.toNat+length.toNat≤(records+index*120#64).toNat)
    (recordBefore : (records+index*120#64).toNat+120≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) NestedLists.rowArguments=some (Rlp.Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (NestedLists.iteration .authorization)).2.clock≤191*length.toNat+207 := by
  have actual:=NestedLists.iteration_prefix_cost .authorization entry (60*length.toNat+192) args (by
    intro current payloadPointer payloadLength next count items contained payloadBound rows arity frame saved
    change count=6#64 at arity
    subst count
    have currentRecords : current.locals.lookup (ofString "recs")=some (.val (.word records)):=
      (saved (ofString "recs") (by decide) (by decide)).trans recordsCell
    have currentIndex : current.locals.lookup (ofString "i")=some (.val (.word index)):=
      (saved (ofString "i") (by decide) (by decide)).trans indexCell
    have read : eval current recordExpression=some (.val (.word (records+index*120#64))):=by
      simp [recordExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,currentRecords,currentIndex,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
    have price:=fields_cost rows read (by omega) recordBefore
    omega)
  omega

/-- All actual field operations retain unrelated caller bindings on a
continuing path; assigned w remains explicitly excluded. -/
theorem program_saved (key : MlS) (notIndex : key≠ofString "i") (notField : ∀ phase,key≠ofString (fieldName phase)) (phases : List Nat) :
    LocalPrefix key (program phases) := by
  induction phases with
  | nil=>exact .assign _ _ notIndex
  | cons phase rest ih=>
    rw [program]
    split
    · exact .seq (.call (some (ofString (fieldName phase))) _ _ (by intro name same; cases same; exact notField phase)) (.seq (.store _ _) ih)
    · exact .decCall (ofString (fieldName phase)) _ _ _ (notField phase) (.seq (.store _ _) ih)

theorem fields_saved (key : MlS) (notRecord : key≠ofString "a") (notIndex : key≠ofString "i") (notField : ∀ phase,key≠ofString (fieldName phase)) :
    LocalPrefix key (NestedLists.fields .authorization) := by
  rw [fields_shape]
  exact .dec _ _ _ notRecord (program_saved key notIndex notField _)

/-- A real complete authorization iteration preserves all earlier input,
advances its actual outer index and retains a bounded aligned growing heap.
Nested conversion allocation is observed, rather than kept artificially fixed. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap records index : BitVec 64}
    (entry : NestedLists.Entry source pointer length heap)
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (inputBefore : pointer.toNat+length.toNat≤(records+index*120#64).toNat)
    (recordBefore : (records+index*120#64).toNat+120≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) NestedLists.rowArguments=some (Rlp.Header.values pointer length))
    (normal : evaluateHOLFiniteState source (NestedLists.iteration .authorization)=(none,target)) :
    (∃ last,target.globals.lookup (ofString "heap_ptr")=some (.val (.word last)) ∧ AllocatedBytes.Arena last 0 ∧
      last.toNat≤2952790016 ∧ last.toNat%8=0 ∧ heap.toNat≤last.toNat) ∧
      PersistentNormalFrame source target (records+index*120#64) ∧
      target.locals.lookup (ofString "i")=some (.val (.word (index+1#64))) ∧
      (∀ key,key≠ofString "it"→key≠ofString "ent"→key≠ofString "a"→key≠ofString "i"→
        (∀ phase,key≠ofString (fieldName phase))→target.locals.lookup key=source.locals.lookup key) := by
  obtain ⟨current,inner,payloadPointer,payloadLength,next,count,items,contained,payloadBound,rows,arity,prefixFrame,saved,fieldRun,physical,restored,_callerNames,_payloadLower⟩:=
    NestedLists.iteration_prefix_normal .authorization entry args normal
  change count=6#64 at arity
  subst count
  have currentRecords : current.locals.lookup (ofString "recs")=some (.val (.word records)):=
    (saved (ofString "recs") (by decide) (by decide)).trans recordsCell
  have currentIndex : current.locals.lookup (ofString "i")=some (.val (.word index)):=
    (saved (ofString "i") (by decide) (by decide)).trans indexCell
  have read : eval current recordExpression=some (.val (.word (records+index*120#64))):=by
    simp [recordExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,currentRecords,currentIndex,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  obtain ⟨fieldMetadata,fieldMemory⟩:=fields_normal rows read (by omega) recordBefore fieldRun
  have finalRuntime:=(MemoryMetadata.of_frame physical).trans fieldMetadata
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalRuntime
  change target.globals=current.globals at finalGlobals
  obtain ⟨last,cell,arena,bounded,aligned,grows⟩:=prefixFrame.nextHeap
  have restricted : PersistentNormalFrame source current (records+index*120#64):=
    ⟨⟨last,cell,arena,bounded,aligned,by omega⟩,prefixFrame.metadata,prefixFrame.globals,
      by intro query before; exact prefixFrame.memory query (by omega)⟩
  have updated:=restricted.after_memory source current inner (records+index*120#64) fieldMetadata fieldMemory
  have frame:=updated.of_erase source inner source target (records+index*120#64) rfl physical
  have advanced:=fields_advance current inner index currentIndex fieldRun
  refine ⟨⟨last,by rw [finalGlobals]; exact cell,arena,bounded,aligned,grows⟩,frame,
    (restored (ofString "i") (by decide) (by decide)).trans advanced,?_⟩
  intro key notIt notEnt notRecord notIndex notField
  have unchanged:=(fields_saved key notRecord notIndex notField).summary_full current |>.1
  rw [fieldRun] at unchanged
  exact (restored key notIt notEnt).trans ((unchanged rfl).trans (saved key notIt notEnt))

end InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.fields_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.State.reader_resume
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.value_width
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.phase_room
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.State.store_resume
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.program_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.charge_six
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.fields_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.of_readonly

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.State.restored

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.State.store_frame

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.program_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.program_advance

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.fields_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.fields_advance

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.iteration_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.guard_none
#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.iteration_prefix_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.restore_key

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.program_saved

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.fields_saved

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationFields.iteration_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64:=NestedLists.body .authorization
def afterSlices : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match afterSlices with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loopAndReturn : ProgHOL 64:=match afterAllocation with | .dec _ _ _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .lower (localVar "i") (.rfield 1 (localVar "lst"))
abbrev iteration : ProgHOL 64:=NestedLists.iteration .authorization

/-- The current heap is allowed to grow through real per-entry conversions.
Original rows and the complete output allocation remain physically separated. -/
structure Model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array records count : BitVec 64) (items : List Rlp.ListItem) where
  index : BitVec 64
  heap : BitVec 64
  arena : Rlp.LiveArena source
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count)
  recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records))
  bounded : index.toNat≤count.toNat
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  model : Rlp.ListItems source pointer length.toNat items
  rows : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  inputBefore : pointer.toNat+length.toNat≤array.toNat
  arrayBefore : array.toNat+16*count.toNat≤records.toNat
  recordsArena : AllocatedBytes.Arena records (120*count.toNat)
  recordsAligned : records.toNat%8=0
  recordsBefore : records.toNat+120*count.toNat≤heap.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0

theorem Model.destination {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat) :
    (records+data.index*120#64).toNat=records.toNat+120*data.index.toNat ∧
      (records+data.index*120#64).toNat+120≤data.heap.toNat := by
  have room:=data.recordsBefore
  have upper:=data.heapBound
  have product : (data.index*120#64).toNat=120*data.index.toNat:=by
    rw [BitVec.toNat_mul]
    change (data.index.toNat*120)%2^64=120*data.index.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have number : (records+data.index*120#64).toNat=records.toNat+120*data.index.toNat:=by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  exact ⟨number,by rw [number]; omega⟩

theorem Model.select {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat) :
    ∃ item,items[data.index.toNat]?=some item := by
  have inside : data.index.toNat<items.length:=by rw [←data.countExact]; exact active
  exact ⟨items[data.index.toNat],List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩⟩

/-- The selected original row supplies the actual RLP call, physical entry
and record separation used by the complete real iteration. -/
theorem Model.entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[data.index.toNat]?=some item) :
    let itemPointer:=Rlp.Slices.itemPointer pointer items data.index.toNat
    item.total.toNat=item.size ∧ NestedLists.Entry source itemPointer item.total data.heap ∧
      itemPointer.toNat+item.total.toNat≤(records+data.index*120#64).toNat ∧
      (records+data.index*120#64).toNat+120≤data.heap.toNat ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) NestedLists.rowArguments=some (Rlp.Header.values itemPointer item.total) := by
  let itemPointer:=Rlp.Slices.itemPointer pointer items data.index.toNat
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.inputBefore; have upper:=array.isLt; omega
  have spans:=data.model.at_span source pointer length.toNat items data.index.toNat item selected fits
  obtain ⟨offset,path,bounded,valid,encoded⟩:=data.model.at source pointer length.toNat items data.index.toNat item selected
  have itemNumber : itemPointer.toNat=pointer.toNat+offset:=by
    change (Rlp.Slices.itemPointer pointer items data.index.toNat).toNat=_
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inputBound : itemPointer.toNat+item.total.toNat≤pointer.toNat+length.toNat:=by rw [itemNumber,spans.1]; omega
  have destination:=data.destination active
  have beforeRecord : itemPointer.toNat+item.total.toNat≤(records+data.index*120#64).toNat:=by
    rw [destination.1]
    have inputBefore:=data.inputBefore; have arrayBefore:=data.arrayBefore; omega
  have entry : NestedLists.Entry source itemPointer item.total data.heap:=⟨data.arena,data.heapCell,data.heapArena,data.heapBound,data.heapAligned,by omega⟩
  have words:=Rlp.Slices.Records.at source.memory array pointer items data.rows data.index.toNat item selected
  have product : BitVec.ofNat 64 (16*data.index.toNat)=data.index*16#64:=by
    simp [BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]
  rw [product] at words
  have firstMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*data.index.toNat) data.arena.domain data.arrayArena (by omega) data.arrayAligned (by omega)
  have secondMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*data.index.toNat+8) data.arena.domain data.arrayArena (by omega) data.arrayAligned (by omega)
  simp only [byteAddress,BitVec.ofNat_add,product,BitVec.add_assoc] at firstMapped secondMapped
  simp only [BitVec.add_assoc] at words
  refine ⟨spans.1,entry,beforeRecord,destination.2,?_⟩
  simp [NestedLists.rowArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.listCell,data.indexCell,Rlp.Slices.result,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,BitVec.add_assoc,firstMapped,secondMapped,words.1,words.2,itemPointer]

theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[data.index.toNat]?=some item) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤191*item.size+207 := by
  obtain ⟨size,entry,before,room,args⟩:=data.entry active item selected
  have actual:=AuthorizationFields.iteration_cost entry data.recordsCell data.indexCell before room args
  rwa [size] at actual

/-- The same real normal iteration retains the entire original row/input
model while its bounded aligned heap may advance and its index increments. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat)
    (normal : evaluateHOLFiniteState source iteration=(none,target)) :
    ∃ next : Model target pointer length array records count items,next.index=data.index+1#64 ∧
      data.heap.toNat≤next.heap.toNat ∧ PersistentNormalFrame source target records := by
  obtain ⟨item,selected⟩:=data.select active
  obtain ⟨size,entry,before,room,args⟩:=data.entry active item selected
  obtain ⟨⟨heap,heapCell,heapArena,heapBound,heapAligned,grows⟩,frame,indexCell,saved⟩:=AuthorizationFields.iteration_normal entry data.recordsCell data.indexCell before room args normal
  have number:=(data.destination active).1
  have inputBeforeRecord : pointer.toNat+length.toNat≤(records+data.index*120#64).toNat:=by
    rw [number]
    have inputBefore:=data.inputBefore; have arrayBefore:=data.arrayBefore; omega
  have window : Rlp.Slices.Window source target (records+data.index*120#64).toNat (2^64):=by
    intro query outside
    rcases outside with before|after
    · exact frame.memory query before
    · have upper:=query.isLt; omega
  have fits : pointer.toNat+length.toNat<2^64:=by have inputBefore:=data.inputBefore; have upper:=array.isLt; omega
  have domain : target.memaddrs=source.memaddrs:=by
    have projected:=congrArg PanSemStateFiniteExact.memaddrs frame.metadata
    exact projected
  have endian : target.be=source.be:=by
    have projected:=congrArg PanSemStateFiniteExact.be frame.metadata
    exact projected
  have code : target.code=source.code:=by
    have projected:=congrArg PanSemStateFiniteExact.code frame.metadata
    exact projected
  have bytes:=Rlp.Slices.Window.bytes_before source target (records+data.index*120#64).toNat (2^64) pointer length window inputBeforeRecord fits
    domain endian
  have nextModel:=data.model.transport source target pointer length.toNat items length.isLt bytes
  have nextRows:=data.rows.of_interval source target array pointer items (by rw [←data.countExact]; have upper:=data.arrayArena.upper; omega) (by
    intro query above below
    apply frame.memory query
    rw [←data.countExact] at below
    rw [number]
    have arrayBefore:=data.arrayBefore; omega)
  have arena : Rlp.LiveArena target:=data.arena.of_cursors (target:=target) domain code
    (frame.globals _ (by decide)) (frame.globals _ (by decide))
  have nextIndexNumber : (data.index+1#64).toNat=data.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change data.index.toNat+1<2^64; have upper:=count.isLt; omega)]
    rfl
  have savedRecords:=saved (ofString "recs") (by decide) (by decide) (by decide) (by decide) (by intro phase; unfold AuthorizationFields.fieldName; split <;> decide)
  have savedList:=saved (ofString "lst") (by decide) (by decide) (by decide) (by decide) (by intro phase; unfold AuthorizationFields.fieldName; split <;> decide)
  let next : Model target pointer length array records count items:={data with
    index:=data.index+1#64,heap:=heap,arena:=arena,indexCell:=indexCell
    listCell:=savedList.trans data.listCell,recordsCell:=savedRecords.trans data.recordsCell
    bounded:=by rw [nextIndexNumber]; omega,model:=nextModel,rows:=nextRows
    recordsBefore:=by have previous:=data.recordsBefore; omega
    heapCell:=heapCell,heapArena:=heapArena,heapBound:=heapBound,heapAligned:=heapAligned }
  have wholeFrame : PersistentNormalFrame source target records:=⟨⟨heap,heapCell,heapArena,heapBound,heapAligned,by have previous:=data.recordsBefore; omega⟩,
    frame.metadata,frame.globals,by intro query before; exact frame.memory query (by rw [number]; omega)⟩
  exact ⟨next,rfl,grows,wholeFrame⟩

def Model.clocked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (clock : Nat) : Model {source with clock:=clock} pointer length array records count items:=
  {data with arena:=data.arena.of_frame rfl, model:=data.model.transport source ({source with clock:=clock}) pointer length.toNat items length.isLt (by intros; rfl)}

theorem guard_no_control (first second : ProgHOL 64) (decision : PureDecision first)
    (tail : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState source second).1≠some .break ∧ (evaluateHOLFiniteState source second).1≠some .continue)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source (.seq first second)).1≠some .break ∧ (evaluateHOLFiniteState source (.seq first second)).1≠some .continue := by
  have info:=(decision.summary source).2
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at info ⊢
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>exact tail middle
  | some result=>exact info

theorem iteration_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source iteration).1≠some .break ∧ (evaluateHOLFiniteState source iteration).1≠some .continue := by
  unfold iteration
  rw [(NestedLists.shapes .authorization).1]
  apply scoped_no_loop_control
  intro current
  rw [(NestedLists.shapes .authorization).2.1]
  apply guard_no_control _ _ (PureDecision.ite _ (.raised _ _) .skip)
  intro guarded
  apply scoped_no_loop_control
  intro converted
  rw [(NestedLists.shapes .authorization).2.2]
  apply guard_no_control _ _ (PureDecision.ite _ (.raised _ _) .skip)
  intro fields
  exact ((AuthorizationFields.fields_saved (ofString "lst") (by decide) (by decide)
    (by intro phase; unfold AuthorizationFields.fieldName; split <;> decide)).summary_full fields).2.2

def charge : List Rlp.ListItem→Nat→Nat
  | [],_=>0
  | item::items,0=>191*item.size+208+charge items 0
  | _::items,index+1=>charge items index

theorem charge_step (items : List Rlp.ListItem) (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) :
    charge items index=191*item.size+208+charge items (index+1) := by
  induction items generalizing index with
  | nil=>simp at selected
  | cons head items ih=>
    cases index with
    | zero=>have same : head=item:=by simpa using selected
            subst item; rfl
    | succ index=>exact ih index (by simpa using selected)

theorem charge_zero (items : List Rlp.ListItem) : charge items 0=191*(items.map Rlp.ListItem.size).sum+208*items.length := by
  induction items with
  | nil=>rfl
  | cons item items ih=>simp only [charge,List.map_cons,List.sum_cons,List.length_cons,ih]; omega

theorem charge_le_zero (items : List Rlp.ListItem) (index : Nat) : charge items index≤charge items 0 := by
  induction items generalizing index with
  | nil=>simp [charge]
  | cons item items ih=>
    cases index with
    | zero=>exact Nat.le_refl _
    | succ index=>simp only [charge]; have bound:=ih index; omega

theorem Model.charge_bound {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) : charge items data.index.toNat≤399*length.toNat := by
  have bound:=charge_le_zero items data.index.toNat
  rw [charge_zero,data.model.total_size source pointer length.toNat items,←data.countExact] at bound
  have countBound:=data.countBound
  omega

theorem test_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) :
    eval source test=some (.val (.word (if data.index.toNat<count.toNat then 1#64 else 0#64))) := by
  simp [eval,test,evalHOLExact,toExact,localVar,data.indexCell,data.listCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

theorem active_of_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : data.index.toNat<count.toNat := by
  have expected:=test_read data
  by_contra inactive
  rw [if_neg inactive] at expected
  have same : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero same

/-- Each real entry pays once for its parse/fields and enclosing loop tick.
The remaining input-row charge decreases on every actual continuation. -/
theorem loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤charge items data.index.toNat := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (Model current pointer length array records count items)
  let allowance:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>charge items (CounterFlow.counterWord current (ofString "i")).toNat
  have allowance_model (current : PanSemStateFiniteExact 64 Guest.HostMemory) (live : Model current pointer length array records count items) :
      allowance current=charge items live.index.toNat:=by simp [allowance,CounterFlow.counterWord,live.indexCell,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
      current.clock-output.2.clock≤allowance current ∧
        ((output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ current.clock-output.2.clock+allowance output.2≤allowance current):=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=active_of_test live word read nonzero
    obtain ⟨item,selected⟩:=live.select active
    let entered:=live.clocked (current.clock-1)
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have price:=iteration_cost entered active item selected
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
    change current.clock-1-output.2.clock≤191*item.size+207 at price
    change output.2.clock≤current.clock-1 at forward
    have paid : current.clock-output.2.clock≤191*item.size+208:=by omega
    have charged:=charge_step items live.index.toNat item selected
    refine ⟨?_,?_⟩
    · change current.clock-output.2.clock≤allowance current
      rw [allowance_model current live,charged]
      omega
    intro continuing
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((iteration_safe (decClockHOLFinite current)).2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,grows,frame⟩:=iteration_normal entered active run
    change next.index=live.index+1#64 at indexEq
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have bound:=count.isLt; omega)]
      rfl
    refine ⟨⟨next⟩,?_⟩
    change current.clock-output.2.clock+allowance output.2≤allowance current
    rw [allowance_model output.2 next,allowance_model current live,indexEq,number,charged]
    omega
  have priced:=ClockCost.potential_loop source.code test iteration invariant allowance step source rfl ⟨data⟩
  rwa [allowance_model source data] at priced

theorem loop_linear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤399*length.toNat := (loop_cost data).trans data.charge_bound

/-- Real normal loop completion retains its exact final count, bounded
aligned advancing heap, original rows/input and all earlier persistent words. -/
theorem loop_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items)
    (normal : evaluateHOLFiniteState source (.while test iteration)=(none,target)) :
    ∃ final : Model target pointer length array records count items,final.index.toNat=count.toNat ∧
      data.heap.toNat≤final.heap.toNat ∧ PersistentNormalFrame source target records := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : Model current pointer length array records count items,
    data.heap.toNat≤live.heap.toNat ∧ PersistentNormalFrame source current records
  have initialFrame : PersistentNormalFrame source source records:=⟨⟨data.heap,data.heapCell,data.heapArena,data.heapBound,data.heapAligned,by have before:=data.recordsBefore; omega⟩,
    rfl,by intros; rfl,by intros; rfl⟩
  have initial : invariant source:=⟨data,Nat.le_refl _,initialFrame⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,post)→invariant post:=by
    intro current codeEq valid word read nonzero funded post run
    obtain ⟨live,grown,frame⟩:=valid
    let entered:=live.clocked (current.clock-1)
    obtain ⟨next,indexEq,grows,nextFrame⟩:=iteration_normal entered (active_of_test live word read nonzero) run
    have currentFrame : PersistentNormalFrame current post records:=nextFrame.of_erase (decClockHOLFinite current) post current post records rfl rfl
    exact ⟨next,Nat.le_trans grown grows,frame.trans source current post records records currentFrame (Nat.le_refl _)⟩
  obtain ⟨final,grows,frame⟩:=loop_invariant_no_control source.code test iteration iteration_safe invariant step source target rfl initial normal
  have exited:=loop_normal_exit test iteration (fun current=>(iteration_safe current).1) source target normal
  have expected:=test_read final
  have finished : final.index.toNat=count.toNat:=by
    by_cases active : final.index.toNat<count.toNat
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact (by decide : (0#64 : BitVec 64)≠1#64) impossible |>.elim
    · have bounded:=final.bounded; omega
  exact ⟨final,finished,grows,frame⟩

def sliceArguments : List (ExpHOL 64):=BlobHashes.sliceArguments
def allocationArguments : List (ExpHOL 64):=[.panop .mul [.rfield 1 (localVar "lst"),.const 120#64]]

set_option maxRecDepth 100000 in
theorem shapes : body=.decCall (ofString "lst") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") sliceArguments afterSlices ∧
    afterSlices=.decCall (ofString "recs") .one (ofString "alloc") allocationArguments afterAllocation ∧
    afterAllocation=.dec (ofString "i") .one (.const 0#64) loopAndReturn ∧
    loopAndReturn=.seq (.while test iteration) (.return (.rstruct [localVar "recs",.rfield 1 (localVar "lst")])) := by
  simp only [body,afterSlices,afterAllocation,loopAndReturn,test,iteration,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    sliceArguments,BlobHashes.sliceArguments,allocationArguments,Rlp.Slices.resultShape,localVar,
    Guest.Software.guestFn_decode_authorizations,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  trivial

def allocationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records count : BitVec 64) :=
  setVarHOLFinite (ofString "recs") (.val (.word records)) (PersistentAlloc.post {source with clock:=source.clock-1} records (count*120#64))
def loopEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records count : BitVec 64) :=
  QueryBranch.bind (allocationEntry source records count) "i" 0#64

theorem amount {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) : (count*120#64).toNat=120*count.toNat := by
  have countBound:=data.countBound
  have inputBefore:=data.inputBefore
  have arrayBefore:=data.arrayBefore
  have heapBound:=data.heapBound
  rw [BitVec.toNat_mul]
  change (count.toNat*120)%2^64=120*count.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The original slice conversion and this actual output allocation
initialize every outer-loop condition, including empty arrays. -/
def initial_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items)
    (room : records.toNat+(count*120#64).toNat≤2952790016) : Model (loopEntry source records count) pointer length array records count items := by
  have guards:=PersistentAlloc.guards records (count*120#64) room
  rw [amount data] at room
  let entered:=loopEntry source records count
  have live : Rlp.LiveArena entered:=by
    apply data.arena.of_cursors (target:=entered) rfl rfl
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide]
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide]
  have grows:=guards.2.2.1
  rw [amount data] at grows
  have upper:=guards.2.2.2.1
  exact {
    index:=0#64,heap:=PersistentAlloc.rounded records (count*120#64),arena:=live,indexCell:=bind_lookup_same _ _ _
    listCell:=by
      simpa [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "i"≠ofString "lst" from by decide,show ofString "recs"≠ofString "lst" from by decide] using data.listCell
    recordsCell:=by
      simp [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "i"≠ofString "recs" from by decide]
    bounded:=by simp,countExact:=data.countExact,countBound:=data.countBound
    model:=data.itemModel.transport source entered pointer length.toNat items length.isLt (by intros; rfl)
    rows:=data.records,arrayArena:=data.arrayArena,arrayAligned:=data.arrayAligned,inputBefore:=data.inputBefore,arrayBefore:=data.arrayBefore
    recordsArena:=⟨data.heapArena.lower,by omega⟩,recordsAligned:=data.heapAligned,recordsBefore:=grows
    heapCell:=by simp [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=data.heapArena.lower; omega,by omega⟩,heapBound:=upper,heapAligned:=guards.2.2.2.2 }

theorem after_allocation_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items)
    (room : records.toNat+(count*120#64).toNat≤2952790016) :
    (allocationEntry source records count).clock-(evaluateHOLFiniteState (allocationEntry source records count) afterAllocation).2.clock≤399*length.toNat := by
  rw [shapes.2.2.1]
  apply ClockCost.declared_current (allocationEntry source records count) "i" (.const 0#64) 0#64 loopAndReturn (399*length.toNat) rfl
  rw [shapes.2.2.2]
  exact ClockCost.sequence_current (loopEntry source records count) _ _ (399*length.toNat) 0
    (loop_linear (initial_model data room)) (ClockCost.returned _ _)

theorem allocation_return {source child : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (amountCell : callee.lookup (ofString "n")=some (.val (.word (count*120#64)))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PersistentAlloc.body=(some (.returned value),child)) :
    records.toNat+(count*120#64).toNat≤2952790016 ∧
      CallNormal.continuationEntry source child "recs" value=allocationEntry source records count := by
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child records (count*120#64)
    amountCell data.heapCell data.heapBound (Trap.original_code source.code data.arena.code) value normal
  refine ⟨room,?_⟩
  rw [answer]
  have changed:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString "recs") (.val (.word records)) {state with locals:=source.locals}) frame
  simpa only [CallNormal.continuationEntry,allocationEntry,emptyLocalsHOLFinite,PersistentAlloc.post,callEntryStateHOLFinite] using changed

theorem allocation_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (count*120#64)) := by
  simp [allocationArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.listCell,Rlp.Slices.result,valueIsWord,valueWord,panOpHOL]

theorem after_slices_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) :
    source.clock-(evaluateHOLFiniteState source afterSlices).2.clock≤399*length.toNat+2 := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*120#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [shapes.2.1]
  have price:=ClockCost.scoped_reached_current source "recs" .one (ofString "alloc") allocationArguments _ PersistentAlloc.body afterAllocation callee .one 1 (399*length.toNat)
    (allocation_arguments data) called (PersistentAlloc.body_price source.code data.arena.code (callEntryStateHOLFinite source callee) rfl) (by
      intro child value normal checked
      obtain ⟨room,same⟩:=allocation_return data callee amountCell value normal
      change (CallNormal.continuationEntry source child "recs" value).clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source child "recs" value) afterAllocation).2.clock≤399*length.toNat
      rw [same]
      exact after_allocation_cost data room)
  omega

/-- Complete unchanged authorization decoder: actual conversion/output
allocation, every nested parse/field/write, full loop and all stopped outcomes. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (data : BlobHashes.Entry source pointer length heap) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤470*length.toNat+6 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length):=by
    simp [sliceArguments,BlobHashes.sliceArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointerCell,data.lengthCell]
  rw [shapes.1]
  have price:=Rlp.CurrentSlices.scoped_frame_cost source pointer length heap data.arena data.heapCell data.heapBound data.inputBefore
    (by have before:=data.inputBefore; have bound:=data.heapBound; omega) "lst" sliceArguments afterSlices (399*length.toNat+2) args (by
      intro target items count model countExact countBound records room arena domain endian globals
      exact after_slices_cost (BlobHashes.prepared_from_converter data model countExact countBound records room arena globals))
  omega

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_authorizations")=some ([(ofString "p",.one),(ofString "len",.one)],body,Rlp.Slices.resultShape) := by
  have checked:=OriginalCode.indexed code installed 278 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_authorizations) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,NestedLists.body,NestedLists.declaration,Rlp.Slices.resultShape,
    Guest.Software.guestFn_decode_authorizations,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem iteration_no_return : NoReturn.Never iteration := by
  unfold iteration
  rw [(NestedLists.shapes .authorization).1]
  apply NoReturn.scoped_call
  rw [(NestedLists.shapes .authorization).2.1]
  apply NoReturn.sequence
  · intro F source value
    exact ((show PureGuard (NestedLists.itemGuard .authorization) from .ite _ (.raise _ _) .skip).summary source).2 value
  · apply NoReturn.scoped_call
    rw [(NestedLists.shapes .authorization).2.2]
    apply NoReturn.sequence
    · intro F source value
      exact ((show PureGuard (NestedLists.countGuard .authorization) from .ite _ (.raise _ _) .skip).summary source).2 value
    · intro F source value
      exact ((AuthorizationFields.fields_saved (ofString "lst") (by decide) (by decide)
        (by intro phase; unfold AuthorizationFields.fieldName; split <;> decide)).summary_full source).2.1 value

/-- A real while can return its caller's value only through its body.
Finite evaluator clock induction supplies no assumed termination bound. -/
theorem while_no_return (condition : ExpHOL 64) (step : ProgHOL 64) (never : NoReturn.Never step) : NoReturn.Never (.while condition step) := by
  intro F source value
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 F),current.clock=clock→
      (evaluateHOLFiniteState current (.while condition step)).1≠some (.returned value):=by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro current clockEq
      rw [evaluateHOLFiniteState_while_total]
      generalize observed : @evalHOLFinite 64 F _ current (fun query=>Classical.propDecidable (current.memaddrs query)) condition=read
      cases read with
      | none=>simp
      | some read=>
        cases read with
        | rStruct fields=>simp
        | nStruct name fields=>simp
        | val payload=>
          cases payload with
          | word word=>
            simp only
            by_cases nonzero : word≠0
            · rw [if_pos nonzero]
              by_cases zero : current.clock=0
              · rw [if_pos zero]; simp
              · rw [if_neg zero]
                have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) step
                have noReturn:=never (decClockHOLFinite current)
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) step=output at forward noReturn ⊢
                obtain ⟨result,next⟩:=output
                have fixed:=StateSteps.fixed_clock (decClockHOLFinite current) next result forward
                rw [fixed]
                have earlier : next.clock<clock:=by change next.clock≤current.clock-1 at forward; omega
                have tail:=ih next.clock earlier next rfl
                cases result with
                | none=>exact tail
                | some result=>
                  cases result with
                  | «continue»=>exact tail
                  | returned returned=>exact (noReturn returned rfl).elim
                  | «break»=>simp
                  | error=>simp
                  | timeOut=>simp
                  | exception name payload=>simp
                  | finalFfi event=>simp
            · rw [if_neg nonzero]; simp
  exact auxiliary source.clock source rfl

/-- Actual normal allocation/loop suffix returns the original record pair,
with an observed bounded aligned heap covering all output and the original
input protected. Per-entry nested allocations may advance that heap. -/
theorem after_allocation_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items)
    (room : records.toNat+(count*120#64).toNat≤2952790016) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (allocationEntry source records count) afterAllocation=(some (.returned value),target)) :
    value=Rlp.Slices.result records count ∧
      (∃ last,target.globals.lookup (ofString "heap_ptr")=some (.val (.word last)) ∧
        records.toNat+120*count.toNat≤last.toNat ∧ last.toNat≤2952790016 ∧ last.toNat%8=0) ∧
      PersistentNormalFrame (allocationEntry source records count) target records := by
  rw [shapes.2.2.1] at normal
  obtain ⟨inner,continued,restored⟩:=declaration_return_word (allocationEntry source records count) target "i" (.const 0#64) 0#64 loopAndReturn value rfl normal
  rw [shapes.2.2.2] at continued
  obtain ⟨middle,loopRun,returnRun⟩:=sequence_returned (loopEntry source records count) inner _ _ value
    (while_no_return test iteration iteration_no_return _) continued
  obtain ⟨final,indexEq,grows,frame⟩:=loop_normal (initial_model data room) loopRun
  obtain ⟨read,returned⟩:=return_normal middle inner (.rstruct [localVar "recs",.rfield 1 (localVar "lst")]) value returnRun
  have expected : eval middle (.rstruct [localVar "recs",.rfield 1 (localVar "lst")])=some (Rlp.Slices.result records count):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,final.recordsCell,final.listCell,Rlp.Slices.result]
  have answer:=Option.some.inj (read.symm.trans expected)
  have physical : LocalEffects.erase target=LocalEffects.erase middle:=by rw [restored,returned]; rfl
  have resultFrame:=frame.of_erase (loopEntry source records count) middle (allocationEntry source records count) target records rfl physical
  have globals:=congrArg PanSemStateFiniteExact.globals physical
  change target.globals=middle.globals at globals
  exact ⟨answer,⟨final.heap,by rw [globals]; exact final.heapCell,final.recordsBefore,final.heapBound,final.heapAligned⟩,resultFrame⟩

theorem after_slices_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned value),target)) :
    records.toNat+120*count.toNat≤2952790016 ∧ value=Rlp.Slices.result records count ∧
      (∃ last,target.globals.lookup (ofString "heap_ptr")=some (.val (.word last)) ∧
        records.toNat+120*count.toNat≤last.toNat ∧ last.toNat≤2952790016 ∧ last.toNat%8=0) ∧
      PersistentNormalFrame source target records := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*120#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [shapes.2.1] at normal
  obtain ⟨funded,child,allocated,inner,allocationRun,checked,suffixRun,restored⟩:=CallNormal.scoped_normal source target "recs" .one (ofString "alloc") allocationArguments _
    PersistentAlloc.body afterAllocation callee .one (allocation_arguments data) called value normal
  obtain ⟨room,entryEq⟩:=allocation_return data callee amountCell allocated allocationRun
  rw [entryEq] at suffixRun
  obtain ⟨answer,outputHeap,suffixFrame⟩:=after_allocation_normal data room value suffixRun
  have allocationFrame:=PersistentAlloc.post_persistent_frame source records (count*120#64) data.heapArena room
  have entryFrame:=allocationFrame.of_erase source (PersistentAlloc.post source records (count*120#64)) source (allocationEntry source records count) records rfl rfl
  have composed:=entryFrame.trans source (allocationEntry source records count) inner records records suffixFrame (Nat.le_refl _)
  have frame:=composed.of_erase source inner source target records rfl (by rw [restored]; rfl)
  refine ⟨?_,answer,?_,frame⟩
  · rwa [amount data] at room
  · obtain ⟨last,cell,covered,bounded,aligned⟩:=outputHeap
    exact ⟨last,by rw [restored]; exact cell,covered,bounded,aligned⟩

/-- Genuine normal output of the complete unchanged authorization decoder:
its own aligned allocated120-byte records/count pair, bounded aligned current
heap covering all records, and persistent input/nonheap-global frame. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (data : BlobHashes.Entry source pointer length heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ records count,value=Rlp.Slices.result records count ∧ count.toNat≤length.toNat ∧
      AllocatedBytes.Arena records (120*count.toNat) ∧ records.toNat%8=0 ∧
      (∃ last,target.globals.lookup (ofString "heap_ptr")=some (.val (.word last)) ∧
        records.toNat+120*count.toNat≤last.toNat ∧ last.toNat≤2952790016 ∧ last.toNat%8=0) ∧
      PersistentNormalFrame source target heap := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length):=by
    simp [sliceArguments,BlobHashes.sliceArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointerCell,data.lengthCell]
  rw [shapes.1] at normal
  obtain ⟨funded,child,items,count,inner,model,countExact,countBound,rows,room,arena,domain,endian,globals,window,metadata,above,clock,price,suffixRun,restored⟩:=
    Rlp.CurrentSlices.scoped_normal source target pointer length heap data.arena data.heapCell data.heapBound data.inputBefore
      (by have before:=data.inputBefore; have bound:=data.heapBound; omega) "lst" sliceArguments afterSlices args value normal
  let ready:=CallNormal.continuationEntry source child "lst" (Rlp.Slices.result heap count)
  let records:=PersistentAlloc.rounded heap (count*16#64)
  have prepared:=BlobHashes.prepared_from_converter data model countExact countBound rows room arena globals
  obtain ⟨outputRoom,answer,outputHeap,outputFrame⟩:=after_slices_normal prepared value suffixRun
  change records.toNat+120*count.toNat≤2952790016 at outputRoom
  have converterFrame:=Rlp.CurrentSlices.persistent_frame_of_return source child heap count data.heapArena room metadata window
  have readyFrame:=converterFrame.of_erase source child source ready heap rfl rfl
  have grows : heap.toNat≤records.toNat:=by
    have next:=prepared.arrayBefore
    change heap.toNat+16*count.toNat≤records.toNat at next
    omega
  have composed:=readyFrame.trans source ready inner heap records outputFrame grows
  have frame:=composed.of_erase source inner source target heap rfl (by rw [restored]; rfl)
  refine ⟨records,count,answer,countBound,⟨prepared.heapArena.lower,by omega⟩,prepared.heapAligned,?_,frame⟩
  obtain ⟨last,cell,covered,bounded,aligned⟩:=outputHeap
  exact ⟨last,by rw [restored]; exact cell,covered,bounded,aligned⟩

end InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.Model.destination
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.Model.select
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.Model.entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.iteration_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.Model.clocked

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.guard_no_control

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.iteration_safe

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.charge_step

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.charge_zero

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.charge_le_zero

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.Model.charge_bound

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.test_read

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.active_of_test

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.loop_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.loop_linear

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.loop_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.shapes

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.amount

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.initial_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.after_allocation_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.allocation_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.allocation_arguments

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.after_slices_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.body_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.iteration_no_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.while_no_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.after_allocation_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.after_slices_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AuthorizationLoop.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccessKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- These are extracted from the actual access-list field suffix; the
inner copy loop is checked with its own actual caller bindings. -/
def afterAddress : ProgHOL 64:=match NestedLists.fields .access with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterList : ProgHOL 64:=match afterAddress with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterSlots : ProgHOL 64:=match afterList with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterKeys : ProgHOL 64:=match afterSlots with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loopAndRecord : ProgHOL 64:=match afterKeys with | .dec _ _ _ rest=>rest | _=>.skip
def recordTail : ProgHOL 64:=match loopAndRecord with | .seq _ rest=>rest | _=>.skip

def test : ExpHOL 64:=.cmp .lower (localVar "j") (.rfield 1 (localVar "slots"))
def iteration : ProgHOL 64:=match loopAndRecord with | .seq (.while _ rest) _=>rest | _=>.skip
def readerArguments : List (ExpHOL 64):=[.rfield 0 (localVar "slots"),localVar "j",.const 32#64]
def copyArguments : List (ExpHOL 64):=[.op .add [localVar "keys",.panop .mul [localVar "j",.const 32#64]],localVar "k",.const 32#64]
def copyCall : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy") copyArguments
def increment : ProgHOL 64:=.assign .local (ofString "j") (.op .add [localVar "j",.const 1#64])
def footer : ProgHOL 64:=.seq copyCall increment

set_option maxRecDepth 100000 in
theorem iteration_shape : iteration=.decCall (ofString "k") .one (ofString "tx_fixed_bytes") readerArguments footer := by
  simp only [iteration,loopAndRecord,afterKeys,afterSlots,afterList,afterAddress,NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    readerArguments,footer,copyCall,copyArguments,increment,localVar,Guest.Software.guestFn_decode_access_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

set_option maxRecDepth 100000 in
theorem loop_shape : loopAndRecord=.seq (.while test iteration) recordTail := by
  simp only [loopAndRecord,afterKeys,afterSlots,afterList,afterAddress,NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    iteration,recordTail,test,localVar,Guest.Software.guestFn_decode_access_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

/-- Real stored slice rows and the allocated output buffer during copying.
The item geometry comes from the actual earlier RLP converter. -/
structure LoopModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array buffer count : BitVec 64) (items : List Rlp.ListItem) where
  index : BitVec 64
  arena : Rlp.LiveArena source
  indexCell : source.locals.lookup (ofString "j")=some (.val (.word index))
  listCell : source.locals.lookup (ofString "slots")=some (Rlp.Slices.result array count)
  bufferCell : source.locals.lookup (ofString "keys")=some (.val (.word buffer))
  bounded : index.toNat≤count.toNat
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  totalBytes : (items.map Rlp.ListItem.size).sum=length.toNat
  records : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+16*count.toNat≤buffer.toNat
  bufferArena : AllocatedBytes.Arena buffer (32*count.toNat)
  bufferAligned : buffer.toNat%8=0
  bufferBound : buffer.toNat+32*count.toNat≤2952790016
  spans : ∀ index item,items[index]?=some item →
    item.total.toNat=item.size ∧ (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat<2^64

/-- Exact arithmetic of the actual32-byte destination slot. -/
theorem LoopModel.destination {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat) :
    (buffer+model.index*32#64).toNat=buffer.toNat+32*model.index.toNat ∧
      (buffer+model.index*32#64).toNat%8=0 ∧ (buffer+model.index*32#64).toNat+32<2^64 := by
  have room:=model.bufferBound
  have product : (model.index*32#64).toNat=32*model.index.toNat:=by
    rw [BitVec.toNat_mul]
    change (model.index.toNat*32)%2^64=32*model.index.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have number : (buffer+model.index*32#64).toNat=buffer.toNat+32*model.index.toNat:=by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  exact ⟨number,by rw [number]; have aligned:=model.bufferAligned; omega,by rw [number]; omega⟩

theorem LoopModel.select {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat) :
    ∃ item,items[model.index.toNat]?=some item := by
  have inside : model.index.toNat<items.length:=by rw [←model.countExact]; exact active
  exact ⟨items[model.index.toNat],List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩⟩

/-- Each actual array row supplies the genuine fixed32 reader entry. -/
theorem LoopModel.reader_entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[model.index.toNat]?=some item) :
    ∃ callee,evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) readerArguments=
        some [.val (.word array),.val (.word model.index),.val (.word 32#64)] ∧
      lookupCodeHOLFinite source.code.lookup (ofString "tx_fixed_bytes") [.val (.word array),.val (.word model.index),.val (.word 32#64)]=
        some (TransactionFields.body .fixed,callee,.one) ∧
      TransactionNumbers.Row (callEntryStateHOLFinite source callee) array model.index (Rlp.Slices.itemPointer pointer items model.index.toNat) item.total ∧
      callee.lookup (ofString "width")=some (.val (.word 32#64)) := by
  obtain ⟨callee,called,aCell,iCell,widthCell⟩:=word_triple_environment source.code.lookup (ofString "tx_fixed_bytes") (ofString "arr") (ofString "i") (ofString "width")
    (TransactionFields.body .fixed) .one array model.index 32#64 (by decide) (by decide) (by decide)
    (TransactionFields.original_code .fixed source.code model.arena.code)
  have words:=Rlp.Slices.Records.at source.memory array pointer items model.records model.index.toNat item selected
  have product : BitVec.ofNat 64 (16*model.index.toNat)=model.index*16#64:=by
    simp [BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]
  rw [product] at words
  have firstMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*model.index.toNat) model.arena.domain model.arrayArena (by omega) model.arrayAligned (by omega)
  have secondMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*model.index.toNat+8) model.arena.domain model.arrayArena (by omega) model.arrayAligned (by omega)
  simp only [byteAddress,BitVec.ofNat_add,product] at firstMapped secondMapped
  exact ⟨callee,by simp [readerArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.listCell,model.indexCell,Rlp.Slices.result],called,
    ⟨model.arena.of_frame rfl,aCell,iCell,firstMapped,by
      change source.memaddrs (array+model.index*16#64+8#64)
      simpa only [BitVec.add_assoc] using secondMapped,words.1,words.2,(model.spans _ _ selected).2⟩,widthCell⟩

/-- A literal32-byte copy and increment cost at most42 ticks on every
outcome, independently of whether the copied source is mapped. -/
theorem footer_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source footer).2.clock≤42 := by
  have copyPrice:=BufferDynamicCost.copy_cost source (.op .add [localVar "keys",.panop .mul [localVar "j",.const 32#64]]) (localVar "k") (.const 32#64) 32 installed (by decide) rfl
  exact ClockCost.sequence_current source copyCall increment 42 0 copyPrice (ClockCost.assign source.code _ _)

/-- The real selected row, its fixed reader and memcpy are charged once. -/
theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[model.index.toNat]?=some item) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤60*item.size+54 := by
  obtain ⟨callee,args,called,row,widthCell⟩:=model.reader_entry active item selected
  have price:=TransactionFields.body_cost (callEntryStateHOLFinite source callee) .fixed _ _ row.arena row.fits row.arguments
  rw [iteration_shape]
  have total:=ClockCost.scoped_reached_current source "k" .one (ofString "tx_fixed_bytes") readerArguments _ (TransactionFields.body .fixed) footer callee .one
    (60*item.total.toNat+11) 42 args called price (by
      intro child returned normal checked
      have codeEq:=(evaluation_fields (callEntryStateHOLFinite source callee) child (TransactionFields.body .fixed) (some (.returned returned)) normal).2.2.2
      exact footer_cost (CallNormal.continuationEntry source child "k" returned) (by change OriginalCode.Installed child.code; rw [codeEq]; exact model.arena.code))
  rw [(model.spans _ _ selected).1] at total
  omega

/-- A normally continuing actual iteration retains its slice array and
all earlier input, and advances exactly one initialized output slot. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (active : model.index.toNat<count.toNat)
    (normal : evaluateHOLFiniteState source iteration=(none,target)) :
    ∃ next : LoopModel target pointer length array buffer count items,next.index=model.index+1#64 ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query := by
  obtain ⟨item,selected⟩:=model.select active
  obtain ⟨callee,args,called,row,widthCell⟩:=model.reader_entry active item selected
  rw [iteration_shape] at normal
  obtain ⟨funded,child,returned,inner,fieldRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source target "k" .one (ofString "tx_fixed_bytes")
    readerArguments _ (TransactionFields.body .fixed) footer callee .one args called normal
  obtain ⟨header,valid,valueEq,parseFrame⟩:=TransactionFields.body_fixed_normal (callEntryStateHOLFinite source callee) child _ _ 32#64 row.arena row.fits row.arguments widthCell returned fieldRun
  let resumed:=CallNormal.continuationEntry source child "k" returned
  have resumed_saved (name : String) (different : ofString "k"≠ofString name) :
      resumed.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    simp [resumed,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
  have hCell : resumed.locals.lookup (ofString "k")=some (.val (.word (Rlp.Slices.itemPointer pointer items model.index.toNat+header))):=by
    simp [resumed,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueEq]
  have iCell : resumed.locals.lookup (ofString "j")=some (.val (.word model.index)):= (resumed_saved "j" (by decide)).trans model.indexCell
  have bCell : resumed.locals.lookup (ofString "keys")=some (.val (.word buffer)):= (resumed_saved "keys" (by decide)).trans model.bufferCell
  obtain ⟨copied,copyRun,incrementRun⟩:=sequence_none resumed inner copyCall increment continued
  have copyArgs : evalListHOLFinite resumed (h:=fun query=>Classical.propDecidable (resumed.memaddrs query)) copyArguments=
      some (CopyGeneral.values (buffer+model.index*32#64) (Rlp.Slices.itemPointer pointer items model.index.toNat+header) 32):=by
    simp [copyArguments,CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,bCell,iCell,hCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  have installed : OriginalCode.Installed resumed.code:=by
    change OriginalCode.Installed child.code
    rw [MemoryMetadata.code parseFrame.metadata]
    exact model.arena.code
  obtain ⟨copyFrame,copyLocals⟩:=CopyAny.call_span_normal resumed copied (buffer+model.index*32#64)
    (Rlp.Slices.itemPointer pointer items model.index.toNat+header) 32 (by decide) copyArguments copyArgs installed copyRun
  have copiedIndex : copied.locals.lookup (ofString "j")=some (.val (.word model.index)):=by rw [copyLocals]; exact iCell
  have read : eval copied (.op .add [localVar "j",.const 1#64])=some (.val (.word (model.index+1#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,copiedIndex,valueIsWord,valueWord,wordOpHOL,wordOp]
  have incrementEq:=assign_none copied inner "j" _ _ read incrementRun
  have metadata : MemoryMetadata.erase target=MemoryMetadata.erase source:=by
    rw [endpoint,incrementEq]
    have copiedMetadata : MemoryMetadata.erase copied=MemoryMetadata.erase resumed:=copyFrame.fields
    exact copiedMetadata.trans parseFrame.metadata
  have older (query : BitVec 64) (before : query.toNat<buffer.toNat) : target.memory query=source.memory query:=by
    obtain ⟨number,aligned,fits⟩:=model.destination active
    have away : CopyGeneral.Away (buffer+model.index*32#64) query 32:=CopyGeneral.Away.after _ _ _ aligned fits (by rw [number]; omega)
    rw [endpoint,incrementEq]
    change copied.memory query=source.memory query
    exact (copyFrame.memory query away).trans (parseFrame.outside query (Or.inl (by have cap:=model.bufferBound; omega)))
  have saved (name : String) (notI : ofString "j"≠ofString name) (notH : ofString "k"≠ofString name) :
      target.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
    rw [endpoint,incrementEq]
    exact (restore_lookup_other source _ "k" name (Ne.symm notH)).trans
      ((bind_lookup_other copied "j" name _ notI).trans
        ((congrArg (fun locals=>locals.lookup (ofString name)) copyLocals).trans (resumed_saved name notH)))
  have nextIndex : target.locals.lookup (ofString "j")=some (.val (.word (model.index+1#64))):=by
    rw [endpoint,incrementEq]
    exact (restore_lookup_other source _ "k" "j" (by decide)).trans (bind_lookup_same _ _ _)
  have indexNumber : (model.index+1#64).toNat=model.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; have upper:=count.isLt; omega)]
    rfl
  have records:=model.records.of_interval source target array pointer items (by
    rw [←model.countExact]; have upper:=model.arrayArena.upper; omega) (by
      intro query above before
      apply older query
      rw [←model.countExact] at before
      have arrayBefore:=model.arrayBefore
      omega)
  let next : LoopModel target pointer length array buffer count items:={model with
    index:=model.index+1#64,arena:=model.arena.of_metadata metadata,indexCell:=nextIndex
    listCell:=(saved "slots" (by decide) (by decide)).trans model.listCell
    bufferCell:=(saved "keys" (by decide) (by decide)).trans model.bufferCell
    bounded:=by rw [indexNumber]; omega,records:=records }
  exact ⟨next,rfl,metadata,older⟩

/- The identical per-row byte charge is shared with the checked blob loop. -/
open BlobHashes (charge charge_step charge_zero charge_le_zero)

theorem LoopModel.charge_bound {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) : charge items model.index.toNat≤115*length.toNat := by
  have bound:=charge_le_zero items model.index.toNat
  rw [charge_zero,model.totalBytes,←model.countExact] at bound
  have countBound:=model.countBound
  omega

def LoopModel.clocked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (clock : Nat) :
    LoopModel {source with clock:=clock} pointer length array buffer count items :=
  {model with arena:=model.arena.of_frame rfl}

theorem test_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) :
    eval source test=some (.val (.word (if model.index.toNat<count.toNat then 1#64 else 0#64))) := by
  simp [eval,test,evalHOLExact,toExact,localVar,model.indexCell,model.listCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

theorem active_of_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : model.index.toNat<count.toNat := by
  have expected:=test_read model
  by_contra inactive
  rw [if_neg inactive] at expected
  have same : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero same

theorem iteration_limit : LocalPrefix (ofString "slots") iteration := by
  rw [iteration_shape]
  exact .decCall (ofString "k") .one (ofString "tx_fixed_bytes") readerArguments (by decide)
    (.seq (.call none (ofString "memcpy") copyArguments (by intro name impossible; cases impossible)) (.assign _ _ (by decide)))

/-- Linear full-loop allowance from the actual remaining rows. Continuing
bodies spend their own row charge; aborted bodies fit the remaining budget. -/
theorem loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤charge items model.index.toNat := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current pointer length array buffer count items)
  let allowance:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>charge items (CounterFlow.counterWord current (ofString "j")).toNat
  have allowance_model (current : PanSemStateFiniteExact 64 Guest.HostMemory) (live : LoopModel current pointer length array buffer count items) :
      allowance current=charge items live.index.toNat:=by simp [allowance,CounterFlow.counterWord,live.indexCell,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
      current.clock-output.2.clock≤allowance current ∧
        ((output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ current.clock-output.2.clock+allowance output.2≤allowance current):=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=active_of_test live word read nonzero
    obtain ⟨item,selected⟩:=live.select active
    let entered:=live.clocked (current.clock-1)
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have price:=iteration_cost entered active item selected
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
    change current.clock-1-output.2.clock≤60*item.size+54 at price
    change output.2.clock≤current.clock-1 at forward
    have paid : current.clock-output.2.clock≤60*item.size+55:=by omega
    have charged:=charge_step items live.index.toNat item selected
    refine ⟨?_,?_⟩
    · change current.clock-output.2.clock≤allowance current
      rw [allowance_model current live,charged]
      omega
    intro continuing
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((iteration_limit.summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,metadata,memory⟩:=iteration_normal entered active run
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have bound:=count.isLt; omega)]
      rfl
    have nextNumber : next.index.toNat=live.index.toNat+1:=(congrArg BitVec.toNat indexEq).trans number
    refine ⟨⟨next⟩,?_⟩
    change current.clock-output.2.clock+allowance output.2≤allowance current
    rw [allowance_model current live,allowance_model output.2 next,nextNumber,charged]
    omega
  have priced:=ClockCost.potential_loop source.code test iteration invariant allowance step source rfl ⟨model⟩
  rwa [allowance_model source model] at priced

/-- All real byte extents are charged once, giving a linear loop budget. -/
theorem loop_linear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤115*length.toNat :=
  (loop_cost model).trans model.charge_bound

/-- Actual normal loop completion retains the allocated buffers, restored
runtime metadata, unchanged earlier input and the final checked row count. -/
theorem loop_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (model : LoopModel source pointer length array buffer count items)
    (normal : evaluateHOLFiniteState source (.while test iteration)=(none,target)) :
    ∃ final : LoopModel target pointer length array buffer count items,final.index.toNat=count.toNat ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel current pointer length array buffer count items,
    MemoryMetadata.erase current=MemoryMetadata.erase source ∧ ∀ query : BitVec 64,query.toNat<buffer.toNat→current.memory query=source.memory query
  have initial : invariant source:=⟨model,rfl,by intros; rfl⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,post)→invariant post:=by
    intro current codeEq valid word read nonzero funded post run
    obtain ⟨live,metadata,memory⟩:=valid
    let entered:=live.clocked (current.clock-1)
    obtain ⟨next,indexEq,nextMetadata,nextMemory⟩:=iteration_normal entered (active_of_test live word read nonzero) run
    exact ⟨next,nextMetadata.trans metadata,fun query before=>(nextMemory query before).trans (memory query before)⟩
  obtain ⟨final,metadata,memory⟩:=loop_invariant_no_control source.code test iteration (fun current=>(iteration_limit.summary_full current).2.2)
    invariant step source target rfl initial normal
  have exited:=loop_normal_exit test iteration (fun current=>(iteration_limit.summary_full current).2.2.1) source target normal
  have expected:=test_read final
  have finished : final.index.toNat=count.toNat:=by
    by_cases active : final.index.toNat<count.toNat
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact (by decide : (0#64 : BitVec 64)≠1#64) impossible |>.elim
    · have bounded:=final.bounded; omega
  exact ⟨final,finished,metadata,memory⟩


def slotArguments : List (ExpHOL 64):=[.rfield 0 (localVar "sl"),.rfield 1 (localVar "sl")]
def allocationArguments : List (ExpHOL 64):=[.panop .mul [.rfield 1 (localVar "slots"),.const 32#64]]

set_option maxRecDepth 100000 in
theorem setup_shapes : afterList=.decCall (ofString "slots") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") slotArguments afterSlots ∧
    afterSlots=.decCall (ofString "keys") .one (ofString "alloc") allocationArguments afterKeys ∧
    afterKeys=.dec (ofString "j") .one (.const 0#64) loopAndRecord := by
  simp only [afterList,afterSlots,afterKeys,afterAddress,loopAndRecord,NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    slotArguments,allocationArguments,Rlp.Slices.resultShape,localVar,Guest.Software.guestFn_decode_access_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  trivial

set_option maxRecDepth 100000 in
theorem record_tail_quiet (code) : QuietClock.Preserves code recordTail := by
  simp only [recordTail,loopAndRecord,afterKeys,afterSlots,afterList,afterAddress,NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    Guest.Software.guestFn_decode_access_list,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply QuietClock.declared
    | apply QuietClock.sequence
    | exact QuietClock.store code _ _
    | exact QuietClock.assign code _ _

/-- Actual observed slots conversion result before allocating its keys.
No later copy, allocation, record write or outer-index advance is assumed. -/
structure Prepared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array buffer count : BitVec 64) (items : List Rlp.ListItem) where
  arena : Rlp.LiveArena source
  slotsCell : source.locals.lookup (ofString "slots")=some (Rlp.Slices.result array count)
  model : Rlp.ListItems source pointer length.toNat items
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  records : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  arrayBefore : array.toNat+16*count.toNat≤buffer.toNat
  inputBefore : pointer.toNat+length.toNat≤array.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word buffer))
  heapArena : AllocatedBytes.Arena buffer 0
  heapBound : buffer.toNat≤2952790016
  heapAligned : buffer.toNat%8=0

def prepared_from_converter {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap count : BitVec 64} {items : List Rlp.ListItem}
    (entry : NestedLists.Entry source pointer length heap)
    (model : Rlp.ListItems target pointer length.toNat items) (countExact : count.toNat=items.length) (countBound : count.toNat≤length.toNat)
    (records : Rlp.Slices.Records target.memory heap pointer items) (room : heap.toNat+16*count.toNat≤2952790016)
    (arena : Rlp.LiveArena target)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) :
    Prepared (CallNormal.continuationEntry source target "slots" (Rlp.Slices.result heap count)) pointer length heap (PersistentAlloc.rounded heap (count*16#64)) count items := by
  let ready:=CallNormal.continuationEntry source target "slots" (Rlp.Slices.result heap count)
  have amount : (count*16#64).toNat=16*count.toNat:=by
    rw [BitVec.toNat_mul]
    change (count.toNat*16)%2^64=16*count.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have guards:=PersistentAlloc.guards heap (count*16#64) (by rw [amount]; exact room)
  have grows:=guards.2.2.1
  rw [amount] at grows
  have upper:=guards.2.2.2.1
  exact {
    arena:=arena.of_frame rfl
    slotsCell:=by simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    model:=model.transport target ready pointer length.toNat items length.isLt (by intros; rfl)
    countExact:=countExact,countBound:=countBound,records:=records
    arrayArena:=⟨entry.heapArena.lower,by omega⟩,arrayAligned:=entry.heapAligned,arrayBefore:=grows,inputBefore:=entry.inputBefore
    heapCell:=by change target.globals.lookup (ofString "heap_ptr")=_; rw [globals]; simp [HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=entry.heapArena.lower; omega,by omega⟩,heapBound:=upper,heapAligned:=guards.2.2.2.2 }

def allocationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer count : BitVec 64) :=
  setVarHOLFinite (ofString "keys") (.val (.word buffer)) (PersistentAlloc.post {source with clock:=source.clock-1} buffer (count*32#64))
def loopEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer count : BitVec 64) :=QueryBranch.bind (allocationEntry source buffer count) "j" 0#64

theorem Prepared.amount {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) : (count*32#64).toNat=32*count.toNat := by
  have countBound:=data.countBound; have inputBefore:=data.inputBefore; have arrayBefore:=data.arrayBefore; have heapBound:=data.heapBound
  rw [BitVec.toNat_mul]
  change (count.toNat*32)%2^64=32*count.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

def Prepared.loop_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (room : buffer.toNat+(count*32#64).toNat≤2952790016) :
    LoopModel (loopEntry source buffer count) pointer length array buffer count items := by
  rw [data.amount] at room
  let entered:=loopEntry source buffer count
  have live : Rlp.LiveArena entered:=by
    apply data.arena.of_cursors (target:=entered) rfl rfl
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide]
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide]
  exact {
    index:=0#64,arena:=live,indexCell:=bind_lookup_same _ _ _
    listCell:=by
      simpa [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "j"≠ofString "slots" from by decide,show ofString "keys"≠ofString "slots" from by decide] using data.slotsCell
    bufferCell:=by simp [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "j"≠ofString "keys" from by decide]
    bounded:=by simp,countExact:=data.countExact,countBound:=data.countBound,totalBytes:=data.model.total_size source pointer length.toNat items,records:=data.records
    arrayArena:=data.arrayArena,arrayAligned:=data.arrayAligned,arrayBefore:=data.arrayBefore
    bufferArena:=⟨data.heapArena.lower,by omega⟩,bufferAligned:=data.heapAligned,bufferBound:=room
    spans:=by intro index item selected; have fields:=data.model.at_span source pointer length.toNat items index item selected (by have before:=data.inputBefore; have bound:=array.isLt; omega)
              exact ⟨fields.1,fields.2.2.2⟩ }

theorem after_keys_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (room : buffer.toNat+(count*32#64).toNat≤2952790016) :
    (allocationEntry source buffer count).clock-(evaluateHOLFiniteState (allocationEntry source buffer count) afterKeys).2.clock≤115*length.toNat := by
  rw [setup_shapes.2.2]
  apply ClockCost.declared_current (allocationEntry source buffer count) "j" (.const 0#64) 0#64 loopAndRecord (115*length.toNat) rfl
  rw [loop_shape]
  exact ClockCost.sequence_current (loopEntry source buffer count) _ _ (115*length.toNat) 0
    (loop_linear (data.loop_model room)) (ClockCost.of_quiet _ _ (record_tail_quiet _))

theorem allocation_return {source child : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (amountCell : callee.lookup (ofString "n")=some (.val (.word (count*32#64)))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PersistentAlloc.body=(some (.returned value),child)) :
    buffer.toNat+(count*32#64).toNat≤2952790016 ∧ CallNormal.continuationEntry source child "keys" value=allocationEntry source buffer count := by
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child buffer (count*32#64)
    amountCell data.heapCell data.heapBound (Trap.original_code source.code data.arena.code) value normal
  refine ⟨room,?_⟩
  rw [answer]
  have changed:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString "keys") (.val (.word buffer)) {state with locals:=source.locals}) frame
  simpa only [CallNormal.continuationEntry,allocationEntry,emptyLocalsHOLFinite,PersistentAlloc.post,callEntryStateHOLFinite] using changed

theorem allocation_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (count*32#64)) := by
  simp [allocationArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.slotsCell,Rlp.Slices.result,valueIsWord,valueWord,panOpHOL]

theorem after_slots_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) :
    source.clock-(evaluateHOLFiniteState source afterSlots).2.clock≤115*length.toNat+2 := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*32#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [setup_shapes.2.1]
  have price:=ClockCost.scoped_reached_current source "keys" .one (ofString "alloc") allocationArguments _ PersistentAlloc.body afterKeys callee .one 1 (115*length.toNat)
    (allocation_arguments data) called (PersistentAlloc.body_price source.code data.arena.code (callEntryStateHOLFinite source callee) rfl) (by
      intro child value normal checked
      obtain ⟨room,same⟩:=allocation_return data callee amountCell value normal
      change (CallNormal.continuationEntry source child "keys" value).clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source child "keys" value) afterKeys).2.clock≤115*length.toNat
      rw [same]; exact after_keys_cost data room)
  omega

/-- Complete actual access key suffix, including its real slots conversion,
keys allocation, fixed32 copy loop, record stores and outer index advance. -/
theorem after_list_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (entry : NestedLists.Entry source pointer length heap)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) slotArguments=some (Rlp.Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source afterList).2.clock≤186*length.toNat+6 := by
  rw [setup_shapes.1]
  have price:=Rlp.CurrentSlices.scoped_frame_cost source pointer length heap entry.arena entry.heapCell entry.heapBound entry.inputBefore
    (by have before:=entry.inputBefore; have bound:=entry.heapBound; omega) "slots" slotArguments afterSlots (115*length.toNat+2) args (by
      intro target items count model countExact countBound records room arena domain endian globals
      exact after_slots_cost (prepared_from_converter entry model countExact countBound records room arena globals))
  omega

theorem iteration_saved (key : MlS) (notIndex : key≠ofString "j") (notItem : key≠ofString "k") : LocalPrefix key iteration := by
  rw [iteration_shape]
  exact .decCall _ _ _ _ notItem (.seq (.call none _ _ (by intro name impossible; cases impossible)) (.assign _ _ notIndex))

/-- A genuinely continuing key suffix supplies the actual completed copy
state and actual remaining record-store run. It does not assume those stores
succeed in order to establish the copy loop's physical guarantees. -/
theorem after_keys_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array buffer count : BitVec 64} {items : List Rlp.ListItem}
    (data : Prepared source pointer length array buffer count items) (room : buffer.toNat+(count*32#64).toNat≤2952790016)
    (normal : evaluateHOLFiniteState (allocationEntry source buffer count) afterKeys=(none,target)) :
    ∃ current inner,∃ final : LoopModel current pointer length array buffer count items,final.index.toNat=count.toNat ∧
      PersistentNormalFrame source current buffer ∧ MemoryMetadata.erase current=MemoryMetadata.erase (allocationEntry source buffer count) ∧
      evaluateHOLFiniteState current recordTail=(none,inner) ∧
      LocalEffects.erase target=LocalEffects.erase inner ∧
      (∀ key,key≠ofString "j"→key≠ofString "k"→current.locals.lookup key=(allocationEntry source buffer count).locals.lookup key) ∧
      (∀ key,key≠ofString "j"→target.locals.lookup key=inner.locals.lookup key) := by
  rw [setup_shapes.2.2] at normal
  obtain ⟨inside,continued,endpoint⟩:=declaration_none_word (allocationEntry source buffer count) target "j" (.const 0#64) 0#64 loopAndRecord rfl normal
  rw [loop_shape] at continued
  obtain ⟨current,loopRun,tailRun⟩:=sequence_none (loopEntry source buffer count) inside (.while test iteration) recordTail continued
  obtain ⟨final,indexEq,metadata,memory⟩:=loop_normal (data.loop_model room) loopRun
  have allocated:=PersistentAlloc.post_persistent_frame source buffer (count*32#64) data.heapArena room
  have entered:=allocated.of_erase source (PersistentAlloc.post source buffer (count*32#64)) source (loopEntry source buffer count) buffer rfl rfl
  have frame:=entered.after_memory source (loopEntry source buffer count) current buffer metadata memory
  refine ⟨current,inside,final,indexEq,frame,metadata,tailRun,?_,?_,?_⟩
  · rw [endpoint]; rfl
  · intro key notIndex notItem
    have saved:=((LocalPrefix.loop test (iteration_saved key notIndex notItem)).summary_full (loopEntry source buffer count)).1
    rw [loopRun] at saved
    have original : (loopEntry source buffer count).locals.lookup key=(allocationEntry source buffer count).locals.lookup key:=by
      simp [loopEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notIndex,Ne.symm notIndex]
    exact (saved rfl).trans original
  · intro key notIndex
    rw [endpoint]
    exact NestedLists.restore_key _ _ "j" key notIndex

def recordExpression : ExpHOL 64:=.op .add [localVar "recs",.panop .mul [localVar "i",.const 24#64]]
def recordAddress (offset : BitVec 64) : ExpHOL 64:=.op .add [localVar "rec",.const offset]
def recordBody : ProgHOL 64:=.seq (.store (recordAddress 0#64) (localVar "addr"))
  (.seq (.store (recordAddress 8#64) (localVar "keys"))
    (.seq (.store (recordAddress 16#64) (.rfield 1 (localVar "slots")))
      (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))))
def recordMemory (memory : BitVec 64→HolWordLab 64) (record address keys count : BitVec 64) : BitVec 64→HolWordLab 64:=
  StoreWord.put (StoreWord.put (StoreWord.put memory record address) (record+8#64) keys) (record+16#64) count

set_option maxRecDepth 100000 in
theorem record_shape : recordTail=.dec (ofString "rec") .one recordExpression recordBody := by
  simp only [recordTail,loopAndRecord,afterKeys,afterSlots,afterList,afterAddress,NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    recordExpression,recordAddress,recordBody,localVar,Guest.Software.guestFn_decode_access_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]

/-- The three actually observed scalar stores write exactly address, keys
and key count; actual outer-index assignment and lexical restoration retain
all other physical fields. No future store success is an input premise. -/
theorem record_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {records index address buffer array count : BitVec 64}
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (keysCell : source.locals.lookup (ofString "keys")=some (.val (.word buffer)))
    (slotsCell : source.locals.lookup (ofString "slots")=some (Rlp.Slices.result array count))
    (normal : evaluateHOLFiniteState source recordTail=(none,target)) :
    MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      target.memory=recordMemory source.memory (records+index*24#64) address buffer count ∧
      target.locals.lookup (ofString "i")=some (.val (.word (index+1#64))) ∧
      (∀ key,key≠ofString "rec"→key≠ofString "i"→target.locals.lookup key=source.locals.lookup key) := by
  let record:=records+index*24#64
  have recordRead : eval source recordExpression=some (.val (.word record)):=by
    simp [record,recordExpression,eval,evalHOLExact,evalListHOLExact,toExact,localVar,recordsCell,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]
  rw [record_shape] at normal
  obtain ⟨inner,continued,endpoint⟩:=declaration_none_word source target "rec" recordExpression record recordBody recordRead normal
  let entered:=QueryBranch.bind source "rec" record
  obtain ⟨first,firstRun,afterFirst⟩:=sequence_none entered inner (.store (recordAddress 0#64) (localVar "addr")) _ continued
  obtain ⟨second,secondRun,afterSecond⟩:=sequence_none first inner (.store (recordAddress 8#64) (localVar "keys")) _ afterFirst
  obtain ⟨third,thirdRun,incrementRun⟩:=sequence_none second inner (.store (recordAddress 16#64) (.rfield 1 (localVar "slots"))) _ afterSecond
  have read0 : eval entered (recordAddress 0#64)=some (.val (.word record)):=by
    simp [entered,recordAddress,eval,evalHOLExact,evalListHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueIsWord,valueWord,wordOpHOL,wordOp]
  have value0 : eval entered (localVar "addr")=some (.val (.word address)):=by
    simp [entered,eval,evalHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,addressCell,
      show ofString "rec"≠ofString "addr" from by decide]
  obtain ⟨mapped0,firstEq⟩:=word_store_normal entered first _ _ record address read0 value0 firstRun
  rw [firstEq] at secondRun
  have read8 : eval {entered with memory:=StoreWord.put entered.memory record address} (recordAddress 8#64)=some (.val (.word (record+8#64))):=by
    simp [entered,recordAddress,eval,evalHOLExact,evalListHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueIsWord,valueWord,wordOpHOL,wordOp]
  have value8 : eval {entered with memory:=StoreWord.put entered.memory record address} (localVar "keys")=some (.val (.word buffer)):=by
    simp [entered,eval,evalHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,keysCell,
      show ofString "rec"≠ofString "keys" from by decide]
  obtain ⟨mapped8,secondEq⟩:=word_store_normal _ second _ _ (record+8#64) buffer read8 value8 secondRun
  rw [secondEq] at thirdRun
  have read16 : eval {entered with memory:=StoreWord.put (StoreWord.put entered.memory record address) (record+8#64) buffer} (recordAddress 16#64)=some (.val (.word (record+16#64))):=by
    simp [entered,recordAddress,eval,evalHOLExact,evalListHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,valueIsWord,valueWord,wordOpHOL,wordOp]
  have value16 : eval {entered with memory:=StoreWord.put (StoreWord.put entered.memory record address) (record+8#64) buffer} (.rfield 1 (localVar "slots"))=some (.val (.word count)):=by
    simp [entered,eval,evalHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,slotsCell,Rlp.Slices.result,
      show ofString "rec"≠ofString "slots" from by decide]
  obtain ⟨mapped16,thirdEq⟩:=word_store_normal _ third _ _ (record+16#64) count read16 value16 thirdRun
  rw [thirdEq] at incrementRun
  have readIndex : eval {entered with memory:=recordMemory entered.memory record address buffer count} (.op .add [localVar "i",.const 1#64])=some (.val (.word (index+1#64))):=by
    simp [entered,eval,evalHOLExact,evalListHOLExact,toExact,localVar,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      show ofString "rec"≠ofString "i" from by decide]
  have incrementEq:=assign_none {entered with memory:=recordMemory entered.memory record address buffer count} inner "i" _ _ readIndex incrementRun
  refine ⟨?_,?_,?_,?_⟩
  · rw [endpoint,incrementEq]; rfl
  · rw [endpoint,incrementEq]; rfl
  · rw [endpoint,incrementEq]
    exact (restore_lookup_other source _ "rec" "i" (by decide)).trans (bind_lookup_same _ _ _)
  · intro key notRecord notIndex
    rw [endpoint,incrementEq,NestedLists.restore_key _ _ "rec" key notRecord]
    simp [entered,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notIndex,notRecord,Ne.symm notIndex,Ne.symm notRecord]

/-- Exact scalar writes preserve both sides of the actual24-byte record.
No destination mapping or successful future memory read is assumed. -/
theorem record_memory_window (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (record address buffer count : BitVec 64)
    (fits : record.toNat+24<2^64) (memory : target.memory=recordMemory source.memory record address buffer count) :
    Rlp.Slices.Window source target record.toNat (record.toNat+24) := by
  have number8 : (record+8#64).toNat=record.toNat+8:=by rw [BitVec.toNat_add_of_lt (by change record.toNat+8<2^64; omega)]; rfl
  have number16 : (record+16#64).toNat=record.toNat+16:=by rw [BitVec.toNat_add_of_lt (by change record.toNat+16<2^64; omega)]; rfl
  intro query outside
  have not0 : query≠record:=by intro same; subst query; omega
  have not8 : query≠record+8#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number8] at number; omega
  have not16 : query≠record+16#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number16] at number; omega
  rw [memory]
  simp [recordMemory,StoreWord.put,not0,not8,not16]

/-- The real stored record retains all three actual values at distinct
word addresses, making its nested key pointer/count available to later code. -/
theorem record_memory_values (memory : BitVec 64→HolWordLab 64) (record address buffer count : BitVec 64) (fits : record.toNat+24<2^64) :
    recordMemory memory record address buffer count record=.word address ∧
      recordMemory memory record address buffer count (record+8#64)=.word buffer ∧
      recordMemory memory record address buffer count (record+16#64)=.word count := by
  have number8 : (record+8#64).toNat=record.toNat+8:=by rw [BitVec.toNat_add_of_lt (by change record.toNat+8<2^64; omega)]; rfl
  have number16 : (record+16#64).toNat=record.toNat+16:=by rw [BitVec.toNat_add_of_lt (by change record.toNat+16<2^64; omega)]; rfl
  have not8 : record≠record+8#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number8] at number; omega
  have not16 : record≠record+16#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number16] at number; omega
  have distinct : record+8#64≠record+16#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number8,number16] at number; omega
  simp [recordMemory,StoreWord.put,not8,not16,distinct]

/-- The observed nested-key result written into one actual access record.
All pointers/counts, room and heap growth come from this same execution. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length heap record index address : BitVec 64) where
  buffer : BitVec 64
  count : BitVec 64
  last : BitVec 64
  countBound : count.toNat≤length.toNat
  bufferArena : AllocatedBytes.Arena buffer (32*count.toNat)
  bufferAligned : buffer.toNat%8=0
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word last))
  heapArena : AllocatedBytes.Arena last 0
  heapBound : last.toNat≤2952790016
  heapAligned : last.toNat%8=0
  grows : heap.toNat≤last.toNat
  bufferBefore : buffer.toNat+32*count.toNat≤last.toNat
  addressStored : target.memory record=.word address
  bufferStored : target.memory (record+8#64)=.word buffer
  countStored : target.memory (record+16#64)=.word count
  frame : PersistentNormalFrame source target record
  indexCell : target.locals.lookup (ofString "i")=some (.val (.word (index+1#64)))
  saved : ∀ key,key≠ofString "slots"→key≠ofString "keys"→key≠ofString "j"→key≠ofString "k"→key≠ofString "rec"→key≠ofString "i"→
    target.locals.lookup key=source.locals.lookup key

/-- Lift a real nested normal result through its genuine reader prefix
and saved-caller scope restoration. Temporary bindings are restored even
when the tracked key is the scoped name itself. -/
def Output.scoped {source child inner : PanSemStateFiniteExact 64 Guest.HostMemory} {small large heap record index address : BitVec 64}
    (name : String) (value : ValueHOL 64)
    (output : Output (CallNormal.continuationEntry source child name value) inner small heap record index address)
    (bounded : small.toNat≤large.toNat)
    (prefixFrame : PersistentNormalFrame source (CallNormal.continuationEntry source child name value) record)
    (notIndex : ofString name≠ofString "i") : Output source (restore source name inner) large heap record index address := by
  have composed:=prefixFrame.trans source (CallNormal.continuationEntry source child name value) inner record record output.frame (Nat.le_refl _)
  refine {output with
    countBound:=Nat.le_trans output.countBound bounded
    frame:=composed.of_erase source inner source (restore source name inner) record rfl rfl
    indexCell:=(NestedLists.restore_key source inner name (ofString "i") (Ne.symm notIndex)).trans output.indexCell
    saved:=?_ }
  intro key notSlots notKeys notJ notK notRecord notI
  by_cases same : key=ofString name
  · subst key
    exact NestedLists.restore_key_same source inner name
  · have original : (CallNormal.continuationEntry source child name value).locals.lookup key=source.locals.lookup key:=by
      simp [CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,same,Ne.symm same]
    exact (NestedLists.restore_key source inner name key same).trans ((output.saved key notSlots notKeys notJ notK notRecord notI).trans original)

/-- The actual slots conversion, keys allocation, copy loop and record
stores derive one real owned key buffer/count record and outer-index advance.
No successful future copy/store or nested allocation is assumed at entry. -/
theorem after_list_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap records index address : BitVec 64}
    (entry : NestedLists.Entry source pointer length heap)
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (recordBefore : (records+index*24#64).toNat+24≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) slotArguments=some (Rlp.Header.values pointer length))
    (normal : evaluateHOLFiniteState source afterList=(none,target)) :
    Nonempty (Output source target length heap (records+index*24#64) index address) := by
  rw [setup_shapes.1] at normal
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=entry.inputBefore; have bound:=heap.isLt; omega
  obtain ⟨callee,called,pCell,nCell⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") Rlp.Slices.body Rlp.Slices.resultShape pointer length
    (Rlp.Slices.original_code source.code entry.arena.code)
  obtain ⟨funded,slicePost,sliceValue,afterSlotsPost,sliceRun,checked,allocationRun,sliceEndpoint⟩:=CallNormal.scoped_none source target "slots" Rlp.Slices.resultShape (ofString "rlp_list_to_slices") slotArguments _ Rlp.Slices.body afterSlots callee Rlp.Slices.resultShape args called normal
  obtain ⟨items,count,model,countExact,countBound,answer,rows,room,arena,globals,window,metadata,above,spent⟩:=Rlp.CurrentSlices.body_normal
    (callEntryStateHOLFinite source callee) slicePost pointer length heap pCell nCell (entry.arena.of_frame rfl) entry.heapCell entry.heapBound entry.inputBefore
      (by have before:=entry.inputBefore; have bound:=entry.heapBound; omega) sliceValue sliceRun
  rw [answer] at allocationRun
  let ready:=CallNormal.continuationEntry source slicePost "slots" (Rlp.Slices.result heap count)
  let buffer:=PersistentAlloc.rounded heap (count*16#64)
  have prepared:=prepared_from_converter entry model countExact countBound rows room arena globals
  obtain ⟨allocator,allocCall,amountCell⟩:=PersistentAlloc.environment ready.code.lookup (count*32#64) (PersistentAlloc.original_code ready.code prepared.arena.code)
  rw [setup_shapes.2.1] at allocationRun
  obtain ⟨allocFunded,allocPost,allocValue,afterKeysPost,allocRun,allocChecked,keyRun,allocEndpoint⟩:=CallNormal.scoped_none ready afterSlotsPost "keys" .one (ofString "alloc") allocationArguments _ PersistentAlloc.body afterKeys allocator .one (allocation_arguments prepared) allocCall allocationRun
  obtain ⟨keyRoom,keyEntry⟩:=allocation_return prepared allocator amountCell allocValue allocRun
  rw [keyEntry] at keyRun
  obtain ⟨current,inner,final,finished,keyFrame,copyMetadata,recordRun,copyPhysical,copySaved,copyRestored⟩:=after_keys_normal prepared keyRoom keyRun
  have converter:=Rlp.CurrentSlices.persistent_frame_of_return source slicePost heap count entry.heapArena room metadata window
  have converted:=converter.of_erase source slicePost source ready heap rfl rfl
  have heapBeforeBuffer : heap.toNat≤buffer.toNat:=by
    have bound:=prepared.arrayBefore
    change heap.toNat+16*count.toNat≤buffer.toNat at bound
    omega
  have prefixFrame:=converted.trans source ready current heap buffer keyFrame heapBeforeBuffer
  have currentSaved (key : MlS) (notSlots : key≠ofString "slots") (notKeys : key≠ofString "keys") (notIndex : key≠ofString "j") (notItem : key≠ofString "k") :
      current.locals.lookup key=source.locals.lookup key:=by
    rw [copySaved key notIndex notItem]
    simp [allocationEntry,ready,CallNormal.continuationEntry,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,notSlots,notKeys,Ne.symm notSlots,Ne.symm notKeys]
  have currentRecords : current.locals.lookup (ofString "recs")=some (.val (.word records)):=
    (currentSaved _ (by decide) (by decide) (by decide) (by decide)).trans recordsCell
  have currentIndex : current.locals.lookup (ofString "i")=some (.val (.word index)):=
    (currentSaved _ (by decide) (by decide) (by decide) (by decide)).trans indexCell
  have currentAddress : current.locals.lookup (ofString "addr")=some (.val (.word address)):=
    (currentSaved _ (by decide) (by decide) (by decide) (by decide)).trans addressCell
  obtain ⟨recordMetadata,recordMemoryEq,advanced,recordSaved⟩:=record_normal currentRecords currentIndex currentAddress final.bufferCell final.listCell recordRun
  have physical : LocalEffects.erase target=LocalEffects.erase inner:=by rw [sliceEndpoint,allocEndpoint]; exact copyPhysical
  have finalLookup (key : MlS) (notSlots : key≠ofString "slots") (notKeys : key≠ofString "keys") (notIndex : key≠ofString "j") : target.locals.lookup key=inner.locals.lookup key:=by
    rw [sliceEndpoint,allocEndpoint]
    exact (NestedLists.restore_key _ _ "slots" key notSlots).trans ((NestedLists.restore_key _ _ "keys" key notKeys).trans (copyRestored key notIndex))
  have recordFits : (records+index*24#64).toNat+24<2^64:=by have bound:=entry.heapBound; omega
  have recordWindow:=record_memory_window current inner (records+index*24#64) address buffer count recordFits recordMemoryEq
  obtain ⟨observed,observedCell,observedArena,observedBound,observedAligned,observedGrows⟩:=prefixFrame.nextHeap
  have restricted : PersistentNormalFrame source current (records+index*24#64):=⟨⟨observed,observedCell,observedArena,observedBound,observedAligned,by omega⟩,
    prefixFrame.metadata,prefixFrame.globals,by intro query before; exact prefixFrame.memory query (by omega)⟩
  have storedFrame:=restricted.after_memory source current inner (records+index*24#64) recordMetadata (by intro query before; exact recordWindow query (Or.inl before))
  have resultFrame:=storedFrame.of_erase source inner source target (records+index*24#64) rfl physical
  have guards:=PersistentAlloc.guards buffer (count*32#64) keyRoom
  have product : (count*32#64).toNat=32*count.toNat:=prepared.amount
  have covered:=guards.2.2.1
  rw [product] at covered
  have outputBound:=guards.2.2.2.1
  have currentGlobals:=congrArg PanSemStateFiniteExact.globals copyMetadata
  change current.globals=(allocationEntry ready buffer count).globals at currentGlobals
  have finalRuntime:=(MemoryMetadata.of_frame physical).trans recordMetadata
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalRuntime
  change target.globals=current.globals at finalGlobals
  have outputCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded buffer (count*32#64)))):=by
    rw [finalGlobals,currentGlobals]
    simp [allocationEntry,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have finalMemory : target.memory=recordMemory current.memory (records+index*24#64) address buffer count:=
    (LocalEffects.memory_of_erase inner target physical).trans recordMemoryEq
  obtain ⟨addressStored,bufferStored,countStored⟩:=record_memory_values current.memory (records+index*24#64) address buffer count recordFits
  refine ⟨{
    buffer:=buffer,count:=count,last:=PersistentAlloc.rounded buffer (count*32#64),countBound:=countBound
    bufferArena:=final.bufferArena,bufferAligned:=final.bufferAligned,heapCell:=outputCell
    heapArena:=⟨by have lower:=prepared.heapArena.lower; change 2701131776≤buffer.toNat at lower; omega,by omega⟩,heapBound:=outputBound,heapAligned:=guards.2.2.2.2
    grows:=by omega,bufferBefore:=covered
    addressStored:=by rw [finalMemory]; exact addressStored
    bufferStored:=by rw [finalMemory]; exact bufferStored
    countStored:=by rw [finalMemory]; exact countStored
    frame:=resultFrame,indexCell:=(finalLookup _ (by decide) (by decide) (by decide)).trans advanced
    saved:=by
      intro key notSlots notKeys notJ notK notRecord notI
      exact (finalLookup key notSlots notKeys notJ).trans ((recordSaved key notRecord notI).trans (currentSaved key notSlots notKeys notJ notK)) }⟩

end InitECandidate.Solver.Input.CurrentVerify.AccessKeys

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.iteration_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.loop_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.LoopModel.destination

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.LoopModel.select

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.LoopModel.reader_entry

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.footer_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.iteration_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.iteration_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.LoopModel.charge_bound

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.LoopModel.clocked

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.test_read

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.active_of_test

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.iteration_limit

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.loop_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.loop_linear

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.loop_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.setup_shapes

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.record_tail_quiet

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.prepared_from_converter

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.Prepared.amount

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.Prepared.loop_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.after_keys_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.allocation_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.allocation_arguments

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.after_slots_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.after_list_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.iteration_saved

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.after_keys_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.record_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.record_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.record_memory_window

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.record_memory_values

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.after_list_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccessFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch NestedLists

def listArguments : List (ExpHOL 64):=[.rfield 0 (localVar "ent"),.const 1#64]

set_option maxRecDepth 100000 in
theorem shapes : NestedLists.fields .access=.decCall (ofString "addr") .one (ofString "tx_fixed_bytes") (readerArguments .fixed 0#64 20#64) AccessKeys.afterAddress ∧
    AccessKeys.afterAddress=.decCall (ofString "sl") Rlp.Slices.resultShape (ofString "tx_list_item") listArguments AccessKeys.afterList := by
  simp only [AccessKeys.afterAddress,AccessKeys.afterList,NestedLists.fields,NestedLists.afterConversion,NestedLists.afterItem,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    listArguments,readerArguments,Rlp.Slices.resultShape,localVar,Guest.Software.guestFn_decode_access_list,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  trivial

/-- The actual two-formal list reader returns its own contained payload;
that same return supplies the real slots conversion and key allocation entry. -/
theorem after_address_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next 2#64 items) (item : Rlp.ListItem) (selected : items[1]?=some item) :
    source.clock-(evaluateHOLFiniteState source AccessKeys.afterAddress).2.clock≤246*item.size+18 := by
  let itemPointer:=Rlp.Slices.itemPointer pointer items 1
  have spans:=rows.item_span 1 item selected
  obtain ⟨callee,called,aCell,iCell⟩:=word_pair_environment source.code.lookup (ofString "tx_list_item") (ofString "arr") (ofString "i")
    (TransactionFields.body .list) Rlp.Slices.resultShape array 1#64 (by decide) (TransactionFields.original_code .list source.code rows.arena.code)
  have row:=rows.row 1#64 (by decide) item selected callee aCell iCell
  have itemFits : itemPointer.toNat+item.total.toNat<2^64:=row.fits
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) listArguments=some [.val (.word array),.val (.word 1#64)]:=by
    simp [listArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
  have bodyPrice:=TransactionFields.body_cost (callEntryStateHOLFinite source callee) .list itemPointer item.total row.arena row.fits row.arguments
  rw [shapes.2]
  have actual:=ClockCost.scoped_reached_current source "sl" Rlp.Slices.resultShape (ofString "tx_list_item") listArguments _ (TransactionFields.body .list) AccessKeys.afterList callee Rlp.Slices.resultShape
    (60*item.total.toNat+11) (186*item.total.toNat+6) args called bodyPrice (by
      intro child value normal checked
      obtain ⟨header,payload,flag,valid,answer,frame⟩:=TransactionFields.body_pair_normal (callEntryStateHOLFinite source callee) child .list itemPointer item.total
        (Or.inr (Or.inr rfl)) row.arena row.fits row.arguments value normal
      have rest:=valid.result_fields itemPointer header payload flag item.total.toNat
      have payloadNumber : (itemPointer+header).toNat=itemPointer.toNat+header.toNat:=by
        rw [BitVec.toNat_add_of_lt (by omega)]
      let ready:=CallNormal.continuationEntry source child "sl" value
      have runtime : MemoryMetadata.erase ready=MemoryMetadata.erase source:=frame.metadata
      have globals:=congrArg PanSemStateFiniteExact.globals runtime
      change ready.globals=source.globals at globals
      have entry : NestedLists.Entry ready (itemPointer+header) payload next:=⟨rows.arena.of_metadata runtime,
        by rw [globals]; exact rows.heapCell,rows.heapArena,rows.heapBound,rows.heapAligned,by
          have inputBefore:=rows.inputBefore; have arrayBefore:=rows.arrayBefore
          have contained:=spans.2
          change itemPointer.toNat+item.total.toNat≤pointer.toNat+length.toNat at contained
          rw [payloadNumber]; omega⟩
      have slotArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) AccessKeys.slotArguments=some (Rlp.Header.values (itemPointer+header) payload):=by
        simp [ready,AccessKeys.slotArguments,CallNormal.continuationEntry,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
      have suffixPrice:=AccessKeys.after_list_cost entry slotArgs
      change ready.clock-(evaluateHOLFiniteState ready AccessKeys.afterList).2.clock≤186*item.total.toNat+6
      omega)
  rw [spans.1] at actual
  omega

/-- Both actual access fields are parsed once; their real two-row byte sum
and contained key payload bound the complete field/key/store suffix. -/
theorem fields_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next 2#64 items) :
    source.clock-(evaluateHOLFiniteState source (NestedLists.fields .access)).2.clock≤246*length.toNat+30 := by
  have count:=rows.countExact
  change 2=items.length at count
  cases items with
  | nil=>simp at count
  | cons first items=>
    cases items with
    | nil=>simp at count
    | cons second rest=>
      have empty : rest=[]:=by cases rest with | nil=>rfl | cons head tail=>simp only [List.length_cons] at count; omega
      subst rest
      have bytes:=rows.model.total_size source pointer length.toNat [first,second]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at bytes
      rw [shapes.1]
      have price:=rows.reader_cost .fixed 0#64 20#64 (by decide) first (by rfl) "addr" (by decide) AccessKeys.afterAddress (246*second.size+18) (by
        intro child value
        dsimp only
        intro currentRows frame checked
        exact after_address_cost currentRows second (by rfl))
      simp only [readerShape,readerName,readerOverhead] at price
      omega

/-- Complete actual access entry iteration, including its own nested
parsing, both fields, key conversion/copies and all stopped store outcomes. -/
theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (entry : NestedLists.Entry source pointer length heap)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) NestedLists.rowArguments=some (Rlp.Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (NestedLists.iteration .access)).2.clock≤377*length.toNat+45 := by
  have actual:=NestedLists.iteration_prefix_cost .access entry (246*length.toNat+30) args (by
    intro current payloadPointer payloadLength next count items contained payloadBound rows arity frame saved
    change count=2#64 at arity
    subst count
    have price:=fields_cost rows
    omega)
  omega

/-- The same actual two-formal list return supplies its contained key
payload and real suffix output, then restores the original sl binding. -/
theorem after_address_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next records index address : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next 2#64 items) (item : Rlp.ListItem) (selected : items[1]?=some item)
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (recordBefore : (records+index*24#64).toNat+24≤next.toNat)
    (normal : evaluateHOLFiniteState source AccessKeys.afterAddress=(none,target)) :
    Nonempty (AccessKeys.Output source target length next (records+index*24#64) index address) := by
  let itemPointer:=Rlp.Slices.itemPointer pointer items 1
  have spans:=rows.item_span 1 item selected
  obtain ⟨callee,called,aCell,iCell⟩:=word_pair_environment source.code.lookup (ofString "tx_list_item") (ofString "arr") (ofString "i")
    (TransactionFields.body .list) Rlp.Slices.resultShape array 1#64 (by decide) (TransactionFields.original_code .list source.code rows.arena.code)
  have row:=rows.row 1#64 (by decide) item selected callee aCell iCell
  have itemFits : itemPointer.toNat+item.total.toNat<2^64:=row.fits
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) listArguments=some [.val (.word array),.val (.word 1#64)]:=by
    simp [listArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
  rw [shapes.2] at normal
  obtain ⟨funded,child,value,inner,bodyRun,checked,suffixRun,endpoint⟩:=CallNormal.scoped_none source target "sl" Rlp.Slices.resultShape (ofString "tx_list_item") listArguments _ (TransactionFields.body .list)
    AccessKeys.afterList callee Rlp.Slices.resultShape args called normal
  obtain ⟨header,payload,flag,valid,answer,frame⟩:=TransactionFields.body_pair_normal (callEntryStateHOLFinite source callee) child .list itemPointer item.total
    (Or.inr (Or.inr rfl)) row.arena row.fits row.arguments value bodyRun
  have rest:=valid.result_fields itemPointer header payload flag item.total.toNat
  have payloadNumber : (itemPointer+header).toNat=itemPointer.toNat+header.toNat:=by rw [BitVec.toNat_add_of_lt (by omega)]
  let ready:=CallNormal.continuationEntry source child "sl" value
  have callerFrame : Rlp.CurrentItem.Frame source ready:=frame.of_erase rfl rfl
  have runtime:=callerFrame.metadata
  have globals:=congrArg PanSemStateFiniteExact.globals runtime
  change ready.globals=source.globals at globals
  have entry : NestedLists.Entry ready (itemPointer+header) payload next:=⟨rows.arena.of_metadata runtime,
    by rw [globals]; exact rows.heapCell,rows.heapArena,rows.heapBound,rows.heapAligned,by
      have inputBefore:=rows.inputBefore; have arrayBefore:=rows.arrayBefore; have contained:=spans.2
      change itemPointer.toNat+item.total.toNat≤pointer.toNat+length.toNat at contained
      rw [payloadNumber]; omega⟩
  have slotArgs : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) AccessKeys.slotArguments=some (Rlp.Header.values (itemPointer+header) payload):=by
    simp [ready,AccessKeys.slotArguments,CallNormal.continuationEntry,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
  have readyRecords : ready.locals.lookup (ofString "recs")=some (.val (.word records)):=by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "sl"≠ofString "recs" from by decide] using recordsCell
  have readyIndex : ready.locals.lookup (ofString "i")=some (.val (.word index)):=by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "sl"≠ofString "i" from by decide] using indexCell
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "sl"≠ofString "addr" from by decide] using addressCell
  obtain ⟨output⟩:=AccessKeys.after_list_normal entry readyRecords readyIndex readyAddress recordBefore slotArgs suffixRun
  have fits : pointer.toNat+length.toNat<2^64:=by have inputBefore:=rows.inputBefore; have upper:=array.isLt; omega
  have totalBound:=(rows.model.at_span source pointer length.toNat items 1 item selected fits).2.2.1
  have payloadBound : payload.toNat≤length.toNat:=by omega
  have prefixFrame:=(rows.reader_persistent callerFrame).lower_frontier (small:=records+index*24#64) (by omega)
  have lifted:=AccessKeys.Output.scoped "sl" value output payloadBound prefixFrame (by decide)
  rw [endpoint]
  exact ⟨lifted⟩

/-- The complete normal two-field suffix derives the actual fixed20
address pointer, owned stored key buffer/count and advancing heap/index, then
restores both real caller scopes. The address remains inside original input. -/
theorem fields_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array next records index : BitVec 64} {items : List Rlp.ListItem}
    (rows : Rows source pointer length array next 2#64 items)
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (recordBefore : (records+index*24#64).toNat+24≤next.toNat)
    (normal : evaluateHOLFiniteState source (NestedLists.fields .access)=(none,target)) :
    ∃ address,Nonempty (AccessKeys.Output source target length next (records+index*24#64) index address) ∧
      pointer.toNat≤address.toNat ∧ address.toNat+20≤pointer.toNat+length.toNat := by
  have count:=rows.countExact
  change 2=items.length at count
  let first:=items[0]'(by omega)
  let second:=items[1]'(by omega)
  have selected0 : items[0]?=some first:=List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
  have selected1 : items[1]?=some second:=List.getElem?_eq_some_iff.mpr ⟨by omega,rfl⟩
  let itemPointer:=Rlp.Slices.itemPointer pointer items 0
  obtain ⟨callee,called,aCell,iCell,widthCell⟩:=reader_environment source rows.arena.code .fixed array 0#64 20#64
  have row:=rows.row 0#64 (by decide) first selected0 callee aCell iCell
  have itemFits : itemPointer.toNat+first.total.toNat<2^64:=row.fits
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (readerArguments .fixed 0#64 20#64)=some (readerValues .fixed array 0#64 20#64):=by
    simp [readerArguments,readerValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rows.entryCell,Rlp.Slices.result]
  rw [shapes.1] at normal
  obtain ⟨funded,child,value,inner,bodyRun,checked,suffixRun,endpoint⟩:=CallNormal.scoped_none source target "addr" .one (ofString "tx_fixed_bytes")
    (readerArguments .fixed 0#64 20#64) _ (TransactionFields.body .fixed) AccessKeys.afterAddress callee .one args called normal
  obtain ⟨header,valid,answer,frame⟩:=TransactionFields.body_fixed_normal (callEntryStateHOLFinite source callee) child itemPointer first.total 20#64
    row.arena row.fits row.arguments widthCell value bodyRun
  have callerFrame : Rlp.CurrentItem.Frame source child:=frame.of_erase rfl rfl
  let ready:=CallNormal.continuationEntry source child "addr" value
  have currentRows:=rows.reader_resume "addr" value (by decide) callerFrame
  have readyRecords : ready.locals.lookup (ofString "recs")=some (.val (.word records)):=by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "addr"≠ofString "recs" from by decide] using recordsCell
  have readyIndex : ready.locals.lookup (ofString "i")=some (.val (.word index)):=by
    simpa [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "addr"≠ofString "i" from by decide] using indexCell
  have readyAddress : ready.locals.lookup (ofString "addr")=some (.val (.word (itemPointer+header))):=by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
  obtain ⟨output⟩:=after_address_normal currentRows second selected1 readyRecords readyIndex readyAddress recordBefore suffixRun
  have prefixFrame:=(rows.reader_persistent (show Rlp.CurrentItem.Frame source ready from callerFrame.of_erase rfl rfl)).lower_frontier
    (small:=records+index*24#64) (by omega)
  have lifted:=AccessKeys.Output.scoped "addr" value output (large:=length) (Nat.le_refl _) prefixFrame (by decide)
  have rest:=valid.result_fields itemPointer header 20#64 0#64 first.total.toNat
  have addressNumber : (itemPointer+header).toNat=itemPointer.toNat+header.toNat:=by rw [BitVec.toNat_add_of_lt (by omega)]
  have spans:=rows.item_span 0 first selected0
  have before : itemPointer.toNat+first.total.toNat≤pointer.toNat+length.toNat:=spans.2
  have itemNumber : itemPointer.toNat=pointer.toNat:=by cases items <;> rfl
  refine ⟨itemPointer+header,?_,?_,?_⟩
  · rw [endpoint]; exact ⟨lifted⟩
  · rw [addressNumber,itemNumber]; omega
  · rw [addressNumber]; change itemPointer.toNat+header.toNat+(20#64 : BitVec 64).toNat≤pointer.toNat+length.toNat; omega

/-- A genuinely continuing complete access iteration derives its stored
owned key buffer/count and input-contained address, growing heap and actual
index advance, including restoration of both original parser scopes. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap records index : BitVec 64}
    (entry : NestedLists.Entry source pointer length heap)
    (recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (recordBefore : (records+index*24#64).toNat+24≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) NestedLists.rowArguments=some (Rlp.Header.values pointer length))
    (normal : evaluateHOLFiniteState source (NestedLists.iteration .access)=(none,target)) :
    ∃ address,Nonempty (AccessKeys.Output source target length heap (records+index*24#64) index address) ∧
      pointer.toNat≤address.toNat ∧ address.toNat+20≤pointer.toNat+length.toNat := by
  obtain ⟨current,inner,payloadPointer,payloadLength,next,count,items,contained,payloadBound,rows,arity,prefixFrame,saved,fieldRun,physical,restored,callerNames,payloadLower⟩:=
    NestedLists.iteration_prefix_normal .access entry args normal
  change count=2#64 at arity
  subst count
  have currentRecords : current.locals.lookup (ofString "recs")=some (.val (.word records)):=
    (saved (ofString "recs") (by decide) (by decide)).trans recordsCell
  have currentIndex : current.locals.lookup (ofString "i")=some (.val (.word index)):=
    (saved (ofString "i") (by decide) (by decide)).trans indexCell
  have currentGrows : heap.toNat≤next.toNat:=by
    obtain ⟨allocated,cell,arena,bounded,aligned,grows⟩:=prefixFrame.nextHeap
    have same : allocated=next:=by
      simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using Option.some.inj (cell.symm.trans rows.heapCell)
    subst allocated
    exact grows
  obtain ⟨address,⟨output⟩,addressLower,addressEnd⟩:=fields_normal rows currentRecords currentIndex (by omega) fieldRun
  have before : (records+index*24#64).toNat≤heap.toNat:=by omega
  have front:=prefixFrame.lower_frontier (small:=records+index*24#64) before
  have composed:=front.trans source current inner (records+index*24#64) (records+index*24#64) output.frame (Nat.le_refl _)
  have resultFrame:=composed.of_erase source inner source target (records+index*24#64) rfl physical
  have globals:=congrArg PanSemStateFiniteExact.globals physical
  change target.globals=inner.globals at globals
  have memory:=LocalEffects.memory_of_erase inner target physical
  have final : AccessKeys.Output source target length heap (records+index*24#64) index address:={output with
    countBound:=Nat.le_trans output.countBound payloadBound
    heapCell:=by rw [globals]; exact output.heapCell
    grows:=Nat.le_trans currentGrows output.grows
    addressStored:=by rw [memory]; exact output.addressStored
    bufferStored:=by rw [memory]; exact output.bufferStored
    countStored:=by rw [memory]; exact output.countStored
    frame:=resultFrame,indexCell:=(restored _ (by decide) (by decide)).trans output.indexCell
    saved:=by
      intro key notSlots notKeys notJ notK notRecord notI
      by_cases isIt : key=ofString "it"
      · exact callerNames key (Or.inl isIt)
      by_cases isEnt : key=ofString "ent"
      · exact callerNames key (Or.inr isEnt)
      exact (restored key isIt isEnt).trans ((output.saved key notSlots notKeys notJ notK notRecord notI).trans (saved key isIt isEnt)) }
  exact ⟨address,⟨final⟩,Nat.le_trans payloadLower addressLower,by omega⟩

end InitECandidate.Solver.Input.CurrentVerify.AccessFields

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.item_span
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.after_address_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.fields_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.iteration_cost

#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.lower_frontier

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.restore_key_same

#print axioms InitECandidate.Solver.Input.CurrentVerify.NestedLists.Rows.reader_persistent

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessKeys.Output.scoped

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.after_address_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.fields_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessFields.iteration_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccessLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def recordPointer (records : BitVec 64) (index : Nat) : BitVec 64:=records+BitVec.ofNat 64 (24*index)

/-- One actually completed access record. Its own encoded-entry size
bounds its stored key count; buffers are owned and covered by the live heap. -/
structure Stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length records heap : BitVec 64) (index bytes : Nat) where
  address : BitVec 64
  buffer : BitVec 64
  count : BitVec 64
  addressCell : source.memory (recordPointer records index)=.word address
  bufferCell : source.memory (recordPointer records index+8#64)=.word buffer
  countCell : source.memory (recordPointer records index+16#64)=.word count
  addressLower : pointer.toNat≤address.toNat
  addressUpper : address.toNat+20≤pointer.toNat+length.toNat
  countBound : count.toNat≤bytes
  bufferArena : AllocatedBytes.Arena buffer (32*count.toNat)
  bufferAligned : buffer.toNat%8=0
  bufferBefore : buffer.toNat+32*count.toNat≤heap.toNat

/-- A later actual iteration protects all earlier record words. Heap
growth retains the previously derived buffer ownership/end bounds. -/
def Stored.transfer {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length records heap next cutoff : BitVec 64} {index bytes : Nat}
    (stored : Stored source pointer length records heap index bytes) (grows : heap.toNat≤next.toNat)
    (before : (recordPointer records index).toNat+24≤cutoff.toNat)
    (memory : ∀ query : BitVec 64,query.toNat<cutoff.toNat→target.memory query=source.memory query) :
    Stored target pointer length records next index bytes := by
  have upper:=cutoff.isLt
  have number8 : (recordPointer records index+8#64).toNat=(recordPointer records index).toNat+8:=by
    rw [BitVec.toNat_add_of_lt (by change (recordPointer records index).toNat+8<2^64; omega)]; rfl
  have number16 : (recordPointer records index+16#64).toNat=(recordPointer records index).toNat+16:=by
    rw [BitVec.toNat_add_of_lt (by change (recordPointer records index).toNat+16<2^64; omega)]; rfl
  exact {stored with
    addressCell:=(memory _ (by omega)).trans stored.addressCell
    bufferCell:=(memory _ (by rw [number8]; omega)).trans stored.bufferCell
    countCell:=(memory _ (by rw [number16]; omega)).trans stored.countCell
    bufferBefore:=Nat.le_trans stored.bufferBefore grows }

def body : ProgHOL 64:=NestedLists.body .access
def afterSlices : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match afterSlices with | .decCall _ _ _ _ rest=>rest | _=>.skip
def loopAndReturn : ProgHOL 64:=match afterAllocation with | .dec _ _ _ rest=>rest | _=>.skip
def test : ExpHOL 64:=.cmp .lower (localVar "i") (.rfield 1 (localVar "lst"))
abbrev iteration : ProgHOL 64:=NestedLists.iteration .access

/-- The current heap is allowed to grow through real per-entry conversions.
Original rows and the complete output allocation remain physically separated. -/
structure Model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length array records count : BitVec 64) (items : List Rlp.ListItem) where
  index : BitVec 64
  heap : BitVec 64
  arena : Rlp.LiveArena source
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count)
  recordsCell : source.locals.lookup (ofString "recs")=some (.val (.word records))
  bounded : index.toNat≤count.toNat
  countExact : count.toNat=items.length
  countBound : count.toNat≤length.toNat
  model : Rlp.ListItems source pointer length.toNat items
  rows : Rlp.Slices.Records source.memory array pointer items
  arrayArena : AllocatedBytes.Arena array (16*count.toNat)
  arrayAligned : array.toNat%8=0
  inputBefore : pointer.toNat+length.toNat≤array.toNat
  arrayBefore : array.toNat+16*count.toNat≤records.toNat
  recordsArena : AllocatedBytes.Arena records (24*count.toNat)
  recordsAligned : records.toNat%8=0
  recordsBefore : records.toNat+24*count.toNat≤heap.toNat
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  completed : ∀ processed,processed<index.toNat→∃ item,items[processed]?=some item ∧ Nonempty (Stored source pointer length records heap processed item.size)

theorem Model.destination {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat) :
    (records+data.index*24#64).toNat=records.toNat+24*data.index.toNat ∧
      (records+data.index*24#64).toNat+24≤data.heap.toNat := by
  have room:=data.recordsBefore
  have upper:=data.heapBound
  have product : (data.index*24#64).toNat=24*data.index.toNat:=by
    rw [BitVec.toNat_mul]
    change (data.index.toNat*24)%2^64=24*data.index.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have number : (records+data.index*24#64).toNat=records.toNat+24*data.index.toNat:=by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  exact ⟨number,by rw [number]; omega⟩

theorem Model.select {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat) :
    ∃ item,items[data.index.toNat]?=some item := by
  have inside : data.index.toNat<items.length:=by rw [←data.countExact]; exact active
  exact ⟨items[data.index.toNat],List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩⟩

/-- The selected original row supplies the actual RLP call, physical entry
and record separation used by the complete real iteration. -/
theorem Model.entry {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[data.index.toNat]?=some item) :
    let itemPointer:=Rlp.Slices.itemPointer pointer items data.index.toNat
    item.total.toNat=item.size ∧ NestedLists.Entry source itemPointer item.total data.heap ∧
      itemPointer.toNat+item.total.toNat≤(records+data.index*24#64).toNat ∧
      (records+data.index*24#64).toNat+24≤data.heap.toNat ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) NestedLists.rowArguments=some (Rlp.Header.values itemPointer item.total) := by
  let itemPointer:=Rlp.Slices.itemPointer pointer items data.index.toNat
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.inputBefore; have upper:=array.isLt; omega
  have spans:=data.model.at_span source pointer length.toNat items data.index.toNat item selected fits
  obtain ⟨offset,path,bounded,valid,encoded⟩:=data.model.at source pointer length.toNat items data.index.toNat item selected
  have itemNumber : itemPointer.toNat=pointer.toNat+offset:=by
    change (Rlp.Slices.itemPointer pointer items data.index.toNat).toNat=_
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have inputBound : itemPointer.toNat+item.total.toNat≤pointer.toNat+length.toNat:=by rw [itemNumber,spans.1]; omega
  have destination:=data.destination active
  have beforeRecord : itemPointer.toNat+item.total.toNat≤(records+data.index*24#64).toNat:=by
    rw [destination.1]
    have inputBefore:=data.inputBefore; have arrayBefore:=data.arrayBefore; omega
  have entry : NestedLists.Entry source itemPointer item.total data.heap:=⟨data.arena,data.heapCell,data.heapArena,data.heapBound,data.heapAligned,by omega⟩
  have words:=Rlp.Slices.Records.at source.memory array pointer items data.rows data.index.toNat item selected
  have product : BitVec.ofNat 64 (16*data.index.toNat)=data.index*16#64:=by
    simp [BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]
  rw [product] at words
  have firstMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*data.index.toNat) data.arena.domain data.arrayArena (by omega) data.arrayAligned (by omega)
  have secondMapped:=AllocatedBytes.word_mapped source array (16*count.toNat) (16*data.index.toNat+8) data.arena.domain data.arrayArena (by omega) data.arrayAligned (by omega)
  simp only [byteAddress,BitVec.ofNat_add,product,BitVec.add_assoc] at firstMapped secondMapped
  simp only [BitVec.add_assoc] at words
  refine ⟨spans.1,entry,beforeRecord,destination.2,?_⟩
  simp [NestedLists.rowArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.listCell,data.indexCell,Rlp.Slices.result,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,BitVec.add_assoc,firstMapped,secondMapped,words.1,words.2,itemPointer]

theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat)
    (item : Rlp.ListItem) (selected : items[data.index.toNat]?=some item) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤377*item.size+45 := by
  obtain ⟨size,entry,before,room,args⟩:=data.entry active item selected
  have actual:=AccessFields.iteration_cost entry args
  rwa [size] at actual

/-- Natural positions of actual allocated24-byte record slots. -/
theorem Model.record_number {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (index : Nat) (inside : index<count.toNat) :
    (recordPointer records index).toNat=records.toNat+24*index := by
  have room:=data.recordsBefore
  have upper:=data.heapBound
  have product : (BitVec.ofNat 64 (24*index)).toNat=24*index:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [recordPointer,BitVec.toNat_add_of_lt (by rw [product]; omega),product]

theorem Model.record_current {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) : recordPointer records data.index.toNat=records+data.index*24#64 := by
  simp [recordPointer,BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.mul_comm]

/-- The original selected item remains contained in its actual full input;
its starting offset and byte extent are retained for decoded record budgets. -/
theorem Model.item_span {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) :
    item.total.toNat=item.size ∧ pointer.toNat≤(Rlp.Slices.itemPointer pointer items index).toNat ∧
      (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat≤pointer.toNat+length.toNat := by
  have fits : pointer.toNat+length.toNat<2^64:=by have before:=data.inputBefore; have upper:=array.isLt; omega
  have span:=data.model.at_span source pointer length.toNat items index item selected fits
  obtain ⟨offset,path,bounded,valid,encoded⟩:=data.model.at source pointer length.toNat items index item selected
  have number : (Rlp.Slices.itemPointer pointer items index).toNat=pointer.toNat+offset:=by
    rw [path,BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  exact ⟨span.1,by rw [number]; omega,by rw [number,span.1]; omega⟩

/-- Each real normal iteration retains all earlier records, adds its own
actual stored key count/ownership and advances the bounded physical model. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (active : data.index.toNat<count.toNat)
    (normal : evaluateHOLFiniteState source iteration=(none,target)) :
    ∃ next : Model target pointer length array records count items,next.index=data.index+1#64 ∧
      data.heap.toNat≤next.heap.toNat ∧ PersistentNormalFrame source target records := by
  obtain ⟨item,selected⟩:=data.select active
  obtain ⟨size,entry,before,room,args⟩:=data.entry active item selected
  obtain ⟨address,⟨output⟩,addressLower,addressEnd⟩:=AccessFields.iteration_normal entry data.recordsCell data.indexCell room args normal
  have number:=(data.destination active).1
  have inputBeforeRecord : pointer.toNat+length.toNat≤(records+data.index*24#64).toNat:=by
    rw [number]
    have inputBefore:=data.inputBefore; have arrayBefore:=data.arrayBefore; omega
  have window : Rlp.Slices.Window source target (records+data.index*24#64).toNat (2^64):=by
    intro query outside
    rcases outside with before|after
    · exact output.frame.memory query before
    · have upper:=query.isLt; omega
  have fits : pointer.toNat+length.toNat<2^64:=by have inputBefore:=data.inputBefore; have upper:=array.isLt; omega
  have domain : target.memaddrs=source.memaddrs:=by have projected:=congrArg PanSemStateFiniteExact.memaddrs output.frame.metadata; exact projected
  have endian : target.be=source.be:=by have projected:=congrArg PanSemStateFiniteExact.be output.frame.metadata; exact projected
  have code : target.code=source.code:=by have projected:=congrArg PanSemStateFiniteExact.code output.frame.metadata; exact projected
  have bytes:=Rlp.Slices.Window.bytes_before source target (records+data.index*24#64).toNat (2^64) pointer length window inputBeforeRecord fits domain endian
  have nextModel:=data.model.transport source target pointer length.toNat items length.isLt bytes
  have nextRows:=data.rows.of_interval source target array pointer items (by rw [←data.countExact]; have upper:=data.arrayArena.upper; omega) (by
    intro query above below
    apply output.frame.memory query
    rw [←data.countExact] at below
    rw [number]
    have arrayBefore:=data.arrayBefore; omega)
  have arena : Rlp.LiveArena target:=data.arena.of_cursors (target:=target) domain code
    (output.frame.globals _ (by decide)) (output.frame.globals _ (by decide))
  have nextIndexNumber : (data.index+1#64).toNat=data.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change data.index.toNat+1<2^64; have upper:=count.isLt; omega)]
    rfl
  have savedRecords:=output.saved (ofString "recs") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have savedList:=output.saved (ofString "lst") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have spans:=data.item_span data.index.toNat item selected
  have currentRecord:=data.record_current
  have stored : Stored target pointer length records output.last data.index.toNat item.size:={
    address:=address,buffer:=output.buffer,count:=output.count
    addressCell:=by rw [currentRecord]; exact output.addressStored
    bufferCell:=by rw [currentRecord]; exact output.bufferStored
    countCell:=by rw [currentRecord]; exact output.countStored
    addressLower:=Nat.le_trans spans.2.1 addressLower,addressUpper:=Nat.le_trans addressEnd spans.2.2
    countBound:=by rw [←size]; exact output.countBound
    bufferArena:=output.bufferArena,bufferAligned:=output.bufferAligned,bufferBefore:=output.bufferBefore }
  have completed : ∀ processed,processed<(data.index+1#64).toNat→∃ item,items[processed]?=some item ∧ Nonempty (Stored target pointer length records output.last processed item.size):=by
    intro processed inside
    rw [nextIndexNumber] at inside
    by_cases previous : processed<data.index.toNat
    · obtain ⟨oldItem,oldSelected,⟨oldStored⟩⟩:=data.completed processed previous
      have oldNumber:=data.record_number processed (by omega)
      have oldBefore : (recordPointer records processed).toNat+24≤(records+data.index*24#64).toNat:=by rw [oldNumber,number]; omega
      exact ⟨oldItem,oldSelected,⟨oldStored.transfer (next:=output.last) output.grows oldBefore output.frame.memory⟩⟩
    · have same : processed=data.index.toNat:=by omega
      subst processed
      exact ⟨item,selected,⟨stored⟩⟩
  let next : Model target pointer length array records count items:={data with
    index:=data.index+1#64,heap:=output.last,arena:=arena,indexCell:=output.indexCell
    listCell:=savedList.trans data.listCell,recordsCell:=savedRecords.trans data.recordsCell
    bounded:=by rw [nextIndexNumber]; omega,model:=nextModel,rows:=nextRows
    recordsBefore:=by have previous:=data.recordsBefore; have grows:=output.grows; omega
    heapCell:=output.heapCell,heapArena:=output.heapArena,heapBound:=output.heapBound,heapAligned:=output.heapAligned,completed:=completed }
  have wholeFrame:=output.frame.lower_frontier (small:=records) (by rw [number]; omega)
  exact ⟨next,rfl,output.grows,wholeFrame⟩

/-- Clock-only transport retains the exact loop index and previously
completed records; source-indexed provenance is transported through real bytes. -/
def Model.clocked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (clock : Nat) : Model {source with clock:=clock} pointer length array records count items := by
  refine {data with
    arena:=data.arena.of_frame rfl
    model:=data.model.transport source ({source with clock:=clock}) pointer length.toNat items length.isLt (by intros; rfl)
    completed:=?_}
  intro processed before
  obtain ⟨item,selected,⟨stored⟩⟩:=data.completed processed before
  exact ⟨item,selected,⟨{stored with addressCell:=stored.addressCell}⟩⟩

theorem record_limit : LocalPrefix (ofString "lst") AccessKeys.recordTail := by
  rw [AccessKeys.record_shape]
  apply LocalPrefix.dec _ _ _ (by decide)
  unfold AccessKeys.recordBody
  exact .seq (.store _ _) (.seq (.store _ _) (.seq (.store _ _) (.assign _ _ (by decide))))

theorem fields_limit : LocalPrefix (ofString "lst") (NestedLists.fields .access) := by
  rw [AccessFields.shapes.1]
  apply LocalPrefix.decCall _ _ _ _ (by decide)
  rw [AccessFields.shapes.2]
  apply LocalPrefix.decCall _ _ _ _ (by decide)
  rw [AccessKeys.setup_shapes.1]
  apply LocalPrefix.decCall _ _ _ _ (by decide)
  rw [AccessKeys.setup_shapes.2.1]
  apply LocalPrefix.decCall _ _ _ _ (by decide)
  rw [AccessKeys.setup_shapes.2.2]
  apply LocalPrefix.dec _ _ _ (by decide)
  rw [AccessKeys.loop_shape]
  exact .seq (.loop AccessKeys.test (AccessKeys.iteration_saved (ofString "lst") (by decide) (by decide))) record_limit

theorem iteration_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (evaluateHOLFiniteState source iteration).1≠some .break ∧ (evaluateHOLFiniteState source iteration).1≠some .continue := by
  unfold iteration
  rw [(NestedLists.shapes .access).1]
  apply scoped_no_loop_control
  intro current
  rw [(NestedLists.shapes .access).2.1]
  apply AuthorizationLoop.guard_no_control _ _ (PureDecision.ite _ (.raised _ _) .skip)
  intro guarded
  apply scoped_no_loop_control
  intro converted
  rw [(NestedLists.shapes .access).2.2]
  apply AuthorizationLoop.guard_no_control _ _ (PureDecision.ite _ (.raised _ _) .skip)
  intro fields
  exact (fields_limit.summary_full fields).2.2

def charge : List Rlp.ListItem→Nat→Nat
  | [],_=>0
  | item::items,0=>377*item.size+46+charge items 0
  | _::items,index+1=>charge items index

theorem charge_step (items : List Rlp.ListItem) (index : Nat) (item : Rlp.ListItem) (selected : items[index]?=some item) :
    charge items index=377*item.size+46+charge items (index+1) := by
  induction items generalizing index with
  | nil=>simp at selected
  | cons head items ih=>
    cases index with
    | zero=>have same : head=item:=by simpa using selected
            subst item; rfl
    | succ index=>exact ih index (by simpa using selected)

theorem charge_zero (items : List Rlp.ListItem) : charge items 0=377*(items.map Rlp.ListItem.size).sum+46*items.length := by
  induction items with
  | nil=>rfl
  | cons item items ih=>simp only [charge,List.map_cons,List.sum_cons,List.length_cons,ih]; omega

theorem charge_le_zero (items : List Rlp.ListItem) (index : Nat) : charge items index≤charge items 0 := by
  induction items generalizing index with
  | nil=>simp [charge]
  | cons item items ih=>
    cases index with
    | zero=>exact Nat.le_refl _
    | succ index=>simp only [charge]; have bound:=ih index; omega

theorem Model.charge_bound {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) : charge items data.index.toNat≤423*length.toNat := by
  have bound:=charge_le_zero items data.index.toNat
  rw [charge_zero,data.model.total_size source pointer length.toNat items,←data.countExact] at bound
  have countBound:=data.countBound
  omega

theorem test_read {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) :
    eval source test=some (.val (.word (if data.index.toNat<count.toNat then 1#64 else 0#64))) := by
  simp [eval,test,evalHOLExact,toExact,localVar,data.indexCell,data.listCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

theorem active_of_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (word : BitVec 64)
    (read : eval source test=some (.val (.word word))) (nonzero : word≠0#64) : data.index.toNat<count.toNat := by
  have expected:=test_read data
  by_contra inactive
  rw [if_neg inactive] at expected
  have same : word=0#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero same

/-- Each real entry pays once for its parse/fields and enclosing loop tick.
The remaining input-row charge decreases on every actual continuation. -/
theorem loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤charge items data.index.toNat := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (Model current pointer length array records count items)
  let allowance:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>charge items (CounterFlow.counterWord current (ofString "i")).toNat
  have allowance_model (current : PanSemStateFiniteExact 64 Guest.HostMemory) (live : Model current pointer length array records count items) :
      allowance current=charge items live.index.toNat:=by simp [allowance,CounterFlow.counterWord,live.indexCell,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
      current.clock-output.2.clock≤allowance current ∧
        ((output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ current.clock-output.2.clock+allowance output.2≤allowance current):=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=active_of_test live word read nonzero
    obtain ⟨item,selected⟩:=live.select active
    let entered:=live.clocked (current.clock-1)
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have price:=iteration_cost entered active item selected
    have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
    change current.clock-1-output.2.clock≤377*item.size+45 at price
    change output.2.clock≤current.clock-1 at forward
    have paid : current.clock-output.2.clock≤377*item.size+46:=by omega
    have charged:=charge_step items live.index.toNat item selected
    refine ⟨?_,?_⟩
    · change current.clock-output.2.clock≤allowance current
      rw [allowance_model current live,charged]
      omega
    intro continuing
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((iteration_safe (decClockHOLFinite current)).2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2):=Prod.ext normal rfl
    obtain ⟨next,indexEq,grows,frame⟩:=iteration_normal entered active run
    change next.index=live.index+1#64 at indexEq
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have bound:=count.isLt; omega)]
      rfl
    refine ⟨⟨next⟩,?_⟩
    change current.clock-output.2.clock+allowance output.2≤allowance current
    rw [allowance_model output.2 next,allowance_model current live,indexEq,number,charged]
    omega
  have priced:=ClockCost.potential_loop source.code test iteration invariant allowance step source rfl ⟨data⟩
  rwa [allowance_model source data] at priced

theorem loop_linear {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) :
    source.clock-(evaluateHOLFiniteState source (.while test iteration)).2.clock≤423*length.toNat := (loop_cost data).trans data.charge_bound

/-- Real normal loop completion retains its exact final count, bounded
aligned advancing heap, original rows/input and all earlier persistent words. -/
theorem loop_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items)
    (normal : evaluateHOLFiniteState source (.while test iteration)=(none,target)) :
    ∃ final : Model target pointer length array records count items,final.index.toNat=count.toNat ∧
      data.heap.toNat≤final.heap.toNat ∧ PersistentNormalFrame source target records := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : Model current pointer length array records count items,
    data.heap.toNat≤live.heap.toNat ∧ PersistentNormalFrame source current records
  have initialFrame : PersistentNormalFrame source source records:=⟨⟨data.heap,data.heapCell,data.heapArena,data.heapBound,data.heapAligned,by have before:=data.recordsBefore; omega⟩,
    rfl,by intros; rfl,by intros; rfl⟩
  have initial : invariant source:=⟨data,Nat.le_refl _,initialFrame⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word))→word≠0→current.clock≠0→∀ post,
      evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,post)→invariant post:=by
    intro current codeEq valid word read nonzero funded post run
    obtain ⟨live,grown,frame⟩:=valid
    let entered:=live.clocked (current.clock-1)
    obtain ⟨next,indexEq,grows,nextFrame⟩:=iteration_normal entered (active_of_test live word read nonzero) run
    have currentFrame : PersistentNormalFrame current post records:=nextFrame.of_erase (decClockHOLFinite current) post current post records rfl rfl
    exact ⟨next,Nat.le_trans grown grows,frame.trans source current post records records currentFrame (Nat.le_refl _)⟩
  obtain ⟨final,grows,frame⟩:=loop_invariant_no_control source.code test iteration iteration_safe invariant step source target rfl initial normal
  have exited:=loop_normal_exit test iteration (fun current=>(iteration_safe current).1) source target normal
  have expected:=test_read final
  have finished : final.index.toNat=count.toNat:=by
    by_cases active : final.index.toNat<count.toNat
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact (by decide : (0#64 : BitVec 64)≠1#64) impossible |>.elim
    · have bounded:=final.bounded; omega
  exact ⟨final,finished,grows,frame⟩

/-- The actual scalar key count stored in a completed record. -/
def keyCount (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records : BitVec 64) (index : Nat) : BitVec 64:=
  match source.memory (recordPointer records index+16#64) with | .word word=>word

/-- Sum the actual record counts in the same original row order. -/
def keyWork (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records : BitVec 64) : List Rlp.ListItem→Nat→Nat
  | [],_=>0
  | _::items,index=>(keyCount source records index).toNat+keyWork source records items (index+1)

theorem key_work_bound (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records : BitVec 64) (items : List Rlp.ListItem) (index : Nat)
    (bounds : ∀ offset item,items[offset]?=some item→(keyCount source records (index+offset)).toNat≤item.size) :
    keyWork source records items index≤(items.map Rlp.ListItem.size).sum := by
  induction items generalizing index with
  | nil=>simp [keyWork]
  | cons item items ih=>
    have head:=bounds 0 item rfl
    simp only [Nat.add_zero] at head
    have tail:=ih (index+1) (by
      intro offset next selected
      have bound:=bounds (offset+1) next (by simpa using selected)
      have same : index+(offset+1)=(index+1)+offset:=by omega
      rwa [same] at bound)
    simp only [keyWork,List.map_cons,List.sum_cons]
    omega

/-- Complete actual records have a linear TOTAL key count. Each count is
charged to its own original encoded entry, never to a maximum-sized neighbor. -/
theorem Model.key_work_bound {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (finished : data.index.toNat=count.toNat) :
    keyWork source records items 0≤length.toNat := by
  have budget:=InitECandidate.Solver.Input.CurrentVerify.AccessLoop.key_work_bound source records items 0 (by
    intro processed item selected
    obtain ⟨inside,sameItem⟩:=List.getElem?_eq_some_iff.mp selected
    obtain ⟨original,originalSelected,⟨stored⟩⟩:=data.completed processed (by have countExact:=data.countExact; omega)
    have same : original=item:=Option.some.inj (originalSelected.symm.trans selected)
    subst original
    simpa only [Nat.zero_add,keyCount,stored.countCell] using stored.countBound)
  rwa [data.model.total_size source pointer length.toNat items] at budget

def sliceArguments : List (ExpHOL 64):=BlobHashes.sliceArguments
def allocationArguments : List (ExpHOL 64):=[.panop .mul [.rfield 1 (localVar "lst"),.const 24#64]]

set_option maxRecDepth 100000 in
theorem shapes : body=.decCall (ofString "lst") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") sliceArguments afterSlices ∧
    afterSlices=.decCall (ofString "recs") .one (ofString "alloc") allocationArguments afterAllocation ∧
    afterAllocation=.dec (ofString "i") .one (.const 0#64) loopAndReturn ∧
    loopAndReturn=.seq (.while test iteration) (.return (.rstruct [localVar "recs",.rfield 1 (localVar "lst")])) := by
  simp only [body,afterSlices,afterAllocation,loopAndReturn,test,iteration,NestedLists.iteration,NestedLists.body,NestedLists.declaration,
    sliceArguments,BlobHashes.sliceArguments,allocationArguments,Rlp.Slices.resultShape,localVar,
    Guest.Software.guestFn_decode_access_list,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  trivial

def allocationEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records count : BitVec 64) :=
  setVarHOLFinite (ofString "recs") (.val (.word records)) (PersistentAlloc.post {source with clock:=source.clock-1} records (count*24#64))
def loopEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (records count : BitVec 64) :=
  QueryBranch.bind (allocationEntry source records count) "i" 0#64

theorem amount {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) : (count*24#64).toNat=24*count.toNat := by
  have countBound:=data.countBound
  have inputBefore:=data.inputBefore
  have arrayBefore:=data.arrayBefore
  have heapBound:=data.heapBound
  rw [BitVec.toNat_mul]
  change (count.toNat*24)%2^64=24*count.toNat
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The original slice conversion and this actual output allocation
initialize every outer-loop condition, including empty arrays. -/
def initial_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items)
    (room : records.toNat+(count*24#64).toNat≤2952790016) : Model (loopEntry source records count) pointer length array records count items := by
  have guards:=PersistentAlloc.guards records (count*24#64) room
  rw [amount data] at room
  let entered:=loopEntry source records count
  have live : Rlp.LiveArena entered:=by
    apply data.arena.of_cursors (target:=entered) rfl rfl
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide]
    · simp [entered,loopEntry,allocationEntry,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide]
  have grows:=guards.2.2.1
  rw [amount data] at grows
  have upper:=guards.2.2.2.1
  exact {
    index:=0#64,heap:=PersistentAlloc.rounded records (count*24#64),arena:=live,indexCell:=bind_lookup_same _ _ _
    listCell:=by
      simpa [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "i"≠ofString "lst" from by decide,show ofString "recs"≠ofString "lst" from by decide] using data.listCell
    recordsCell:=by
      simp [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
        show ofString "i"≠ofString "recs" from by decide]
    bounded:=by simp,countExact:=data.countExact,countBound:=data.countBound
    model:=data.itemModel.transport source entered pointer length.toNat items length.isLt (by intros; rfl)
    rows:=data.records,arrayArena:=data.arrayArena,arrayAligned:=data.arrayAligned,inputBefore:=data.inputBefore,arrayBefore:=data.arrayBefore
    recordsArena:=⟨data.heapArena.lower,by omega⟩,recordsAligned:=data.heapAligned,recordsBefore:=grows
    heapCell:=by simp [entered,loopEntry,allocationEntry,QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    heapArena:=⟨by have lower:=data.heapArena.lower; omega,by omega⟩,heapBound:=upper,heapAligned:=guards.2.2.2.2
    completed:=by intro processed before; change processed<0 at before; omega }

theorem after_allocation_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items)
    (room : records.toNat+(count*24#64).toNat≤2952790016) :
    (allocationEntry source records count).clock-(evaluateHOLFiniteState (allocationEntry source records count) afterAllocation).2.clock≤423*length.toNat := by
  rw [shapes.2.2.1]
  apply ClockCost.declared_current (allocationEntry source records count) "i" (.const 0#64) 0#64 loopAndReturn (423*length.toNat) rfl
  rw [shapes.2.2.2]
  exact ClockCost.sequence_current (loopEntry source records count) _ _ (423*length.toNat) 0
    (loop_linear (initial_model data room)) (ClockCost.returned _ _)

theorem allocation_return {source child : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (amountCell : callee.lookup (ofString "n")=some (.val (.word (count*24#64)))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PersistentAlloc.body=(some (.returned value),child)) :
    records.toNat+(count*24#64).toNat≤2952790016 ∧
      CallNormal.continuationEntry source child "recs" value=allocationEntry source records count := by
  obtain ⟨answer,room,frame⟩:=PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) child records (count*24#64)
    amountCell data.heapCell data.heapBound (Trap.original_code source.code data.arena.code) value normal
  refine ⟨room,?_⟩
  rw [answer]
  have changed:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString "recs") (.val (.word records)) {state with locals:=source.locals}) frame
  simpa only [CallNormal.continuationEntry,allocationEntry,emptyLocalsHOLFinite,PersistentAlloc.post,callEntryStateHOLFinite] using changed

theorem allocation_arguments {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) allocationArguments=some (PersistentAlloc.values (count*24#64)) := by
  simp [allocationArguments,PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.listCell,Rlp.Slices.result,valueIsWord,valueWord,panOpHOL]

theorem after_slices_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) :
    source.clock-(evaluateHOLFiniteState source afterSlices).2.clock≤423*length.toNat+2 := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*24#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [shapes.2.1]
  have price:=ClockCost.scoped_reached_current source "recs" .one (ofString "alloc") allocationArguments _ PersistentAlloc.body afterAllocation callee .one 1 (423*length.toNat)
    (allocation_arguments data) called (PersistentAlloc.body_price source.code data.arena.code (callEntryStateHOLFinite source callee) rfl) (by
      intro child value normal checked
      obtain ⟨room,same⟩:=allocation_return data callee amountCell value normal
      change (CallNormal.continuationEntry source child "recs" value).clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source child "recs" value) afterAllocation).2.clock≤423*length.toNat
      rw [same]
      exact after_allocation_cost data room)
  omega

/-- Complete unchanged access-list decoder: actual conversion/output
allocation, every nested parse/field/write, full loop and all stopped outcomes. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (data : BlobHashes.Entry source pointer length heap) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤494*length.toNat+6 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length):=by
    simp [sliceArguments,BlobHashes.sliceArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointerCell,data.lengthCell]
  rw [shapes.1]
  have price:=Rlp.CurrentSlices.scoped_frame_cost source pointer length heap data.arena data.heapCell data.heapBound data.inputBefore
    (by have before:=data.inputBefore; have bound:=data.heapBound; omega) "lst" sliceArguments afterSlices (423*length.toNat+2) args (by
      intro target items count model countExact countBound records room arena domain endian globals
      exact after_slices_cost (BlobHashes.prepared_from_converter data model countExact countBound records room arena globals))
  omega

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_access_list")=some ([(ofString "p",.one),(ofString "len",.one)],body,Rlp.Slices.resultShape) := by
  have checked:=OriginalCode.indexed code installed 276 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_access_list) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,NestedLists.body,NestedLists.declaration,Rlp.Slices.resultShape,
    Guest.Software.guestFn_decode_access_list,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

def Stored.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length records heap : BitVec 64} {index bytes : Nat}
    (stored : Stored source pointer length records heap index bytes) (memory : target.memory=source.memory) : Stored target pointer length records heap index bytes :=
  {stored with
    addressCell:=by rw [memory]; exact stored.addressCell
    bufferCell:=by rw [memory]; exact stored.bufferCell
    countCell:=by rw [memory]; exact stored.countCell}

theorem key_work_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (records : BitVec 64) (items : List Rlp.ListItem) (index : Nat)
    (memory : target.memory=source.memory) : keyWork target records items index=keyWork source records items index := by
  induction items generalizing index with
  | nil=>rfl
  | cons item items ih=>simp only [keyWork,keyCount,memory,ih]

/-- All actual completed records, charged to their own original encoded
sizes, together with the linear total of their real stored key counts. -/
structure Summary (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length records count heap : BitVec 64) where
  items : List Rlp.ListItem
  countExact : count.toNat=items.length
  bytesTotal : (items.map Rlp.ListItem.size).sum=length.toNat
  model : Rlp.ListItems source pointer length.toNat items
  completed : ∀ processed,processed<count.toNat→∃ item,items[processed]?=some item ∧ Nonempty (Stored source pointer length records heap processed item.size)
  keyBudget : keyWork source records items 0≤length.toNat

def summary_of_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (finished : data.index.toNat=count.toNat) : Summary source pointer length records count data.heap :=
  ⟨items,data.countExact,data.model.total_size source pointer length.toNat items,data.model,
    by intro processed inside; exact data.completed processed (by omega),data.key_work_bound finished⟩

/-- Real scope restoration and caller return retain the input provenance,
record words/owned buffers and aggregate key budget of the observed output. -/
def Summary.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length records count heap : BitVec 64}
    (data : Summary source pointer length records count heap) (physical : LocalEffects.erase target=LocalEffects.erase source) : Summary target pointer length records count heap := by
  have memory:=LocalEffects.memory_of_erase source target physical
  refine {data with
    model:=data.model.transport source target pointer length.toNat data.items length.isLt (by
      intro offset inside
      exact (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>Rlp.ReadLength.byte state (pointer+offset)) physical).symm)
    completed:=?_
    keyBudget:=by rw [key_work_memory source target records data.items 0 memory]; exact data.keyBudget }
  intro processed inside
  obtain ⟨item,selected,⟨stored⟩⟩:=data.completed processed inside
  exact ⟨item,selected,⟨stored.of_memory memory⟩⟩

/-- Real allocated output pair, its covering current heap and complete
stored-record summary. This contains no assumed future execution. -/
structure BufferResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length records count : BitVec 64) where
  last : BitVec 64
  countBound : count.toNat≤length.toNat
  recordsArena : AllocatedBytes.Arena records (24*count.toNat)
  recordsAligned : records.toNat%8=0
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word last))
  heapArena : AllocatedBytes.Arena last 0
  heapBound : last.toNat≤2952790016
  heapAligned : last.toNat%8=0
  recordsBefore : records.toNat+24*count.toNat≤last.toNat
  summary : Summary source pointer length records count last

def result_of_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : Model source pointer length array records count items) (finished : data.index.toNat=count.toNat) : BufferResult source pointer length records count :=
  ⟨data.heap,data.countBound,data.recordsArena,data.recordsAligned,data.heapCell,data.heapArena,data.heapBound,data.heapAligned,data.recordsBefore,summary_of_model data finished⟩

def BufferResult.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length records count : BitVec 64}
    (data : BufferResult source pointer length records count) (physical : LocalEffects.erase target=LocalEffects.erase source) : BufferResult target pointer length records count := by
  have globals:=congrArg PanSemStateFiniteExact.globals physical
  change target.globals=source.globals at globals
  exact {data with heapCell:=by rw [globals]; exact data.heapCell,summary:=data.summary.of_erase physical}

theorem iteration_no_return : NoReturn.Never iteration := by
  unfold iteration
  rw [(NestedLists.shapes .access).1]
  apply NoReturn.scoped_call
  rw [(NestedLists.shapes .access).2.1]
  apply NoReturn.sequence
  · intro F source value
    exact ((show PureGuard (NestedLists.itemGuard .access) from .ite _ (.raise _ _) .skip).summary source).2 value
  · apply NoReturn.scoped_call
    rw [(NestedLists.shapes .access).2.2]
    apply NoReturn.sequence
    · intro F source value
      exact ((show PureGuard (NestedLists.countGuard .access) from .ite _ (.raise _ _) .skip).summary source).2 value
    · intro F source value
      exact (fields_limit.summary_full source).2.1 value

/-- A genuine normal returning allocation/loop suffix retains the actual
record pair and all completed record/key bounds after its final return. -/
theorem after_allocation_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items)
    (room : records.toNat+(count*24#64).toNat≤2952790016) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (allocationEntry source records count) afterAllocation=(some (.returned value),target)) :
    value=Rlp.Slices.result records count ∧ Nonempty (BufferResult target pointer length records count) ∧
      PersistentNormalFrame (allocationEntry source records count) target records := by
  rw [shapes.2.2.1] at normal
  obtain ⟨inner,continued,restored⟩:=declaration_return_word (allocationEntry source records count) target "i" (.const 0#64) 0#64 loopAndReturn value rfl normal
  rw [shapes.2.2.2] at continued
  obtain ⟨middle,loopRun,returnRun⟩:=sequence_returned (loopEntry source records count) inner _ _ value
    (AuthorizationLoop.while_no_return test iteration iteration_no_return _) continued
  obtain ⟨final,indexEq,grows,frame⟩:=loop_normal (initial_model data room) loopRun
  obtain ⟨read,returned⟩:=return_normal middle inner (.rstruct [localVar "recs",.rfield 1 (localVar "lst")]) value returnRun
  have expected : eval middle (.rstruct [localVar "recs",.rfield 1 (localVar "lst")])=some (Rlp.Slices.result records count):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,final.recordsCell,final.listCell,Rlp.Slices.result]
  have answer:=Option.some.inj (read.symm.trans expected)
  have physical : LocalEffects.erase target=LocalEffects.erase middle:=by rw [restored,returned]; rfl
  have result:=(result_of_model final indexEq).of_erase physical
  have resultFrame:=frame.of_erase (loopEntry source records count) middle (allocationEntry source records count) target records rfl physical
  exact ⟨answer,⟨result⟩,resultFrame⟩

theorem after_slices_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length array records count : BitVec 64} {items : List Rlp.ListItem}
    (data : BlobHashes.Prepared source pointer length array records count items) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterSlices=(some (.returned value),target)) :
    value=Rlp.Slices.result records count ∧ Nonempty (BufferResult target pointer length records count) ∧ PersistentNormalFrame source target records := by
  obtain ⟨callee,called,amountCell⟩:=PersistentAlloc.environment source.code.lookup (count*24#64) (PersistentAlloc.original_code source.code data.arena.code)
  rw [shapes.2.1] at normal
  obtain ⟨funded,child,allocated,inner,allocationRun,checked,suffixRun,restored⟩:=CallNormal.scoped_normal source target "recs" .one (ofString "alloc") allocationArguments _
    PersistentAlloc.body afterAllocation callee .one (allocation_arguments data) called value normal
  obtain ⟨room,entryEq⟩:=allocation_return data callee amountCell allocated allocationRun
  rw [entryEq] at suffixRun
  obtain ⟨answer,⟨output⟩,suffixFrame⟩:=after_allocation_normal data room value suffixRun
  have allocationFrame:=PersistentAlloc.post_persistent_frame source records (count*24#64) data.heapArena room
  have entryFrame:=allocationFrame.of_erase source (PersistentAlloc.post source records (count*24#64)) source (allocationEntry source records count) records rfl rfl
  have composed:=entryFrame.trans source (allocationEntry source records count) inner records records suffixFrame (Nat.le_refl _)
  have physical : LocalEffects.erase target=LocalEffects.erase inner:=by rw [restored]; rfl
  have frame:=composed.of_erase source inner source target records rfl physical
  exact ⟨answer,⟨output.of_erase physical⟩,frame⟩

/-- Complete unchanged access decoder normal result: real owned records
and their stored address/key/count facts, linear aggregate key work, actual
bounded aligned covering heap and original persistent-input/global frame. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (data : BlobHashes.Entry source pointer length heap) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ records count,value=Rlp.Slices.result records count ∧ Nonempty (BufferResult target pointer length records count) ∧ PersistentNormalFrame source target heap := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) sliceArguments=some (Rlp.Header.values pointer length):=by
    simp [sliceArguments,BlobHashes.sliceArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,data.pointerCell,data.lengthCell]
  rw [shapes.1] at normal
  obtain ⟨funded,child,items,count,inner,model,countExact,countBound,rows,room,arena,domain,endian,globals,window,metadata,above,clock,price,suffixRun,restored⟩:=
    Rlp.CurrentSlices.scoped_normal source target pointer length heap data.arena data.heapCell data.heapBound data.inputBefore
      (by have before:=data.inputBefore; have bound:=data.heapBound; omega) "lst" sliceArguments afterSlices args value normal
  let ready:=CallNormal.continuationEntry source child "lst" (Rlp.Slices.result heap count)
  let records:=PersistentAlloc.rounded heap (count*16#64)
  have prepared:=BlobHashes.prepared_from_converter data model countExact countBound rows room arena globals
  obtain ⟨answer,⟨output⟩,outputFrame⟩:=after_slices_normal prepared value suffixRun
  have converterFrame:=Rlp.CurrentSlices.persistent_frame_of_return source child heap count data.heapArena room metadata window
  have readyFrame:=converterFrame.of_erase source child source ready heap rfl rfl
  have grows : heap.toNat≤records.toNat:=by
    have next:=prepared.arrayBefore
    change heap.toNat+16*count.toNat≤records.toNat at next
    omega
  have composed:=readyFrame.trans source ready inner heap records outputFrame grows
  have physical : LocalEffects.erase target=LocalEffects.erase inner:=by rw [restored]; rfl
  have frame:=composed.of_erase source inner source target heap rfl physical
  exact ⟨records,count,answer,⟨output.of_erase physical⟩,frame⟩

end InitECandidate.Solver.Input.CurrentVerify.AccessLoop

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Stored.transfer
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.destination
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.select
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.record_number
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.record_current
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.item_span

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.iteration_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.clocked

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.record_limit

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.fields_limit

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.iteration_safe

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.charge_step

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.charge_zero

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.charge_le_zero

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.charge_bound

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.test_read

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.active_of_test

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.loop_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.loop_linear

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.loop_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.key_work_bound

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Model.key_work_bound

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.shapes

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.amount

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.initial_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.after_allocation_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.allocation_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.allocation_arguments

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.after_slices_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.body_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Stored.of_memory

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.key_work_memory

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.summary_of_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.Summary.of_erase

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.result_of_model

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.BufferResult.of_erase

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.iteration_no_return

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.after_allocation_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.after_slices_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccessLoop.body_normal


namespace InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Extract the real envelope selector from the unchanged transaction decoder.
The later field decoder remains its actual continuation. -/
def body : ProgHOL 64:=match Guest.Software.guestFn_decode_transaction_rlp with | .function fn=>progToHOL fn.body | _=>.skip
def afterEmpty : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip
def afterByte : ProgHOL 64:=match afterEmpty with | .dec _ _ _ rest=>rest | _=>.skip
def afterAllocation : ProgHOL 64:=match afterByte with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterZero : ProgHOL 64:=match afterAllocation with | .seq _ rest=>rest | _=>.skip
def afterRawPointer : ProgHOL 64:=match afterZero with | .seq _ rest=>rest | _=>.skip
def envelopeDeclarations : ProgHOL 64:=match afterRawPointer with | .seq _ rest=>rest | _=>.skip
def afterTop : ProgHOL 64:=match envelopeDeclarations with | .dec _ _ _ rest=>rest | _=>.skip
def afterType : ProgHOL 64:=match afterTop with | .dec _ _ _ rest=>rest | _=>.skip
def selectionAndFields : ProgHOL 64:=match afterType with | .dec _ _ _ rest=>rest | _=>.skip
def selection : ProgHOL 64:=match selectionAndFields with | .seq first _=>first | _=>.skip
def afterSelection : ProgHOL 64:=match selectionAndFields with | .seq _ rest=>rest | _=>.skip
def typedTest : ExpHOL 64:=match selection with | .ite test _ _=>test | _=>.const 0#64
def typedSelection : ProgHOL 64:=match selection with | .ite _ yes _=>yes | _=>.skip
def legacyChoice : ProgHOL 64:=match selection with | .ite _ _ no=>no | _=>.skip
def legacyTest : ExpHOL 64:=match legacyChoice with | .ite test _ _=>test | _=>.const 0#64
def typeUpdates : ProgHOL 64:=match typedSelection with | .seq _ rest=>rest | _=>.skip
def decodeArguments (typed : Bool) : List (ExpHOL 64):=
  if typed then [.op .add [localVar "p",.const 1#64],.op .sub [localVar "len",.const 1#64]] else [localVar "p",localVar "len"]
def decodeCall (typed : Bool) : ProgHOL 64:=.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") (decodeArguments typed)

set_option maxRecDepth 100000 in
theorem selection_shapes : selectionAndFields=.seq selection afterSelection ∧
    selection=.ite typedTest typedSelection legacyChoice ∧
    typedSelection=.seq (decodeCall true) typeUpdates ∧
    legacyChoice=.ite legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64)) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp (maxSteps:=1000000) only [afterSelection,typedTest,typedSelection,typeUpdates,legacyChoice,legacyTest,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,decodeCall,decodeArguments,
    Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,localVar,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]

set_option maxRecDepth 100000 in
/-- The actual type/count assignments protect every other caller binding. -/
theorem updates_saved (key : MlS) (notType : key≠ofString "t") (notCount : key≠ofString "nfields") : LocalPrefix key typeUpdates := by
  simp only [typeUpdates,typedSelection,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply LocalPrefix.seq
    | apply LocalPrefix.ite
    | exact LocalPrefix.skip
    | exact LocalPrefix.assign _ _ notType
    | exact LocalPrefix.assign _ _ notCount

set_option maxRecDepth 100000 in
theorem updates_readonly (code) : LocalEffects.Preserves code typeUpdates := by
  simp only [typeUpdates,typedSelection,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply LocalEffects.sequence
    | apply LocalEffects.conditional
    | exact LocalEffects.skip code
    | exact LocalEffects.assign code _ _

set_option maxRecDepth 100000 in
theorem updates_quiet (code) : QuietClock.Preserves code typeUpdates := by
  simp only [typeUpdates,typedSelection,selection,selectionAndFields,afterType,afterTop,envelopeDeclarations,
    afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,Guest.Software.guestFn_decode_transaction_rlp,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some]
  repeat' first
    | apply QuietClock.sequence
    | apply QuietClock.conditional
    | exact QuietClock.skip code
    | exact QuietClock.assign code _ _

/-- Removing the actual type byte preserves the original nonwrapping span.
The nonempty fact is supplied by the decoder's preceding empty guard. -/
theorem typed_extent (pointer length : BitVec 64) (positive : 1≤length.toNat)
    (fits : pointer.toNat+length.toNat<2^64) :
    (pointer+1#64).toNat=pointer.toNat+1 ∧ (length-1#64).toNat=length.toNat-1 ∧
      (pointer+1#64).toNat+(length-1#64).toNat=pointer.toNat+length.toNat := by
  have first : (pointer+1#64).toNat=pointer.toNat+1:=BitVec.toNat_add_of_lt (by change pointer.toNat+1<2^64; omega)
  have second : (length-1#64).toNat=length.toNat-1:=by
    rw [BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact positive)]
    rfl
  exact ⟨first,second,by omega⟩

theorem decode_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (typed : Bool)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (decodeArguments typed)=
      some (Rlp.Header.values (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length)) := by
  cases typed <;> simp [decodeArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
    pointerCell,lengthCell,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Both actual assigned parser calls cover all stopped outcomes. -/
theorem decode_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (typed : Bool)
    (entry : Rlp.CurrentItem.Entry source pointer length) :
    source.clock-(evaluateHOLFiniteState source (decodeCall typed)).2.clock≤60*length.toNat+13 := by
  let start:=if typed then pointer+1#64 else pointer
  let count:=if typed then length-1#64 else length
  have args:=decode_arguments source pointer length typed entry.pointerCell entry.lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Rlp.Decode.body Rlp.Item.resultShape start count
    (Rlp.Decode.original_code source.code entry.arena.code)
  have extent : start.toNat+count.toNat<2^64:=by
    cases typed
    · exact entry.fits
    · change (pointer+1#64).toNat+(length-1#64).toNat<2^64
      rw [(typed_extent pointer length entry.nonempty entry.fits).2.2]
      exact entry.fits
  have countBound : count.toNat≤length.toNat:=by
    cases typed
    · exact Nat.le_refl _
    · change (length-1#64).toNat≤length.toNat
      rw [(typed_extent pointer length entry.nonempty entry.fits).2.1]
      omega
  have priced:=ClockCost.assigned_current source (some (.local,ofString "top")) (ofString "rlp_decode_fully") (decodeArguments typed)
    _ Rlp.Decode.body callee Rlp.Item.resultShape (60*count.toNat+12) args called
    (Rlp.CurrentDecode.body_cost (callEntryStateHOLFinite source callee) start count pointerLocal lengthLocal (entry.arena.of_frame rfl) extent entry.arena.code)
  change source.clock-(evaluateHOLFiniteState source (decodeCall typed)).2.clock≤60*count.toNat+12+1 at priced
  omega

/-- The actual assigned return supplies a complete parse and its real top
binding, while protecting persistent input and original runtime metadata. -/
theorem decode_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (typed : Bool)
    (entry : Rlp.CurrentItem.Entry source pointer length)
    (normal : evaluateHOLFiniteState source (decodeCall typed)=(none,target)) :
    ∃ answer,Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer ∧
      target.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source target ∧
      ∀ key,key≠ofString "top"→target.locals.lookup key=source.locals.lookup key := by
  let start:=if typed then pointer+1#64 else pointer
  let count:=if typed then length-1#64 else length
  have args:=decode_arguments source pointer length typed entry.pointerCell entry.lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Rlp.Decode.body Rlp.Item.resultShape start count
    (Rlp.Decode.original_code source.code entry.arena.code)
  obtain ⟨funded,values,actual,locals,shape,child,answer,arguments,lookup,run,checked,endpoint⟩:=
    CallNormal.local_data source target (ofString "top") (ofString "rlp_decode_fully") (decodeArguments typed) normal
  have valuesEq:=Option.some.inj (arguments.symm.trans args)
  rw [valuesEq,called] at lookup
  have same:=(Option.some.inj lookup).symm
  have actualEq : actual=Rlp.Decode.body:=congrArg Prod.fst same
  have localsEq : locals=callee:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
  rw [actualEq,localsEq] at run
  have extent : start.toNat+count.toNat<2^64:=by
    cases typed
    · exact entry.fits
    · change (pointer+1#64).toNat+(length-1#64).toNat<2^64
      rw [(typed_extent pointer length entry.nonempty entry.fits).2.2]
      exact entry.fits
  obtain ⟨complete,frame,price⟩:=Rlp.CurrentDecode.body_normal (callEntryStateHOLFinite source callee) child start count
    pointerLocal lengthLocal (entry.arena.of_frame rfl) extent entry.arena.code answer run
  refine ⟨answer,complete,?_,frame.of_erase rfl (by rw [endpoint]; rfl),?_⟩
  · rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · intro key other
    rw [endpoint]
    simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]

/-- At most one complete RLP parse occurs in the actual type selector. -/
theorem selection_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length) :
    source.clock-(evaluateHOLFiniteState source selection).2.clock≤60*length.toNat+13 := by
  rw [selection_shapes.2.1]
  have typedPrice : source.clock-(evaluateHOLFiniteState source typedSelection).2.clock≤60*length.toNat+13:=by
    rw [selection_shapes.2.2.1]
    have priced:=ClockCost.sequence_current source (decodeCall true) typeUpdates (60*length.toNat+13) 0
      (decode_call_cost source pointer length true entry) (ClockCost.of_quiet source.code typeUpdates (updates_quiet source.code))
    simpa only [Nat.add_zero] using priced
  have legacyPrice:=ClockCost.conditional_current source legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64))
    (60*length.toNat+13) 0 (decode_call_cost source pointer length false entry) (ClockCost.raised source.code _ _ source rfl)
  rw [←selection_shapes.2.2.2] at legacyPrice
  simpa only [Nat.max_zero,Nat.max_self] using ClockCost.conditional_current source typedTest typedSelection legacyChoice
    (60*length.toNat+13) (60*length.toNat+13) typedPrice (by simpa only [Nat.max_zero] using legacyPrice)


/-- Real normal selection retains one complete parse within the original
input extent. Type/count assignments do not overwrite the returned top item. -/
theorem selection_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length)
    (normal : evaluateHOLFiniteState source selection=(none,target)) :
    ∃ typed : Bool,∃ answer,Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer ∧
      target.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source target ∧
      ∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→target.locals.lookup key=source.locals.lookup key := by
  rw [selection_shapes.2.1] at normal
  rcases conditional_none source target typedTest typedSelection legacyChoice normal with typedRun|legacyRun
  · rw [selection_shapes.2.2.1] at typedRun
    obtain ⟨middle,decodeRun,updatesRun⟩:=sequence_none source target (decodeCall true) typeUpdates typedRun
    obtain ⟨answer,complete,topCell,frame,saved⟩:=decode_call_normal source middle pointer length true entry decodeRun
    have physical:=updates_readonly middle.code middle rfl
    rw [updatesRun] at physical
    have retained:=(updates_saved (ofString "top") (by decide) (by decide)).summary middle
    rw [updatesRun] at retained
    refine ⟨true,answer,complete,retained.1 rfl |>.trans topCell,(Rlp.CurrentItem.Frame.of_readonly physical).trans frame,?_⟩
    intro key notTop notType notCount
    have kept:=(updates_saved key notType notCount).summary middle
    rw [updatesRun] at kept
    exact (kept.1 rfl).trans (saved key notTop)
  · rw [selection_shapes.2.2.2] at legacyRun
    rcases conditional_none source target legacyTest (decodeCall false) (.raise (ofString "TxErr") (.const 2#64)) legacyRun with decodeRun|rejected
    · obtain ⟨answer,complete,topCell,frame,saved⟩:=decode_call_normal source target pointer length false entry decodeRun
      exact ⟨false,answer,complete,topCell,frame,fun key notTop _ _=>saved key notTop⟩
    · exact False.elim (raise_ne_none source (ofString "TxErr") (.const 2#64) (congrArg Prod.fst rejected))


def emptyGuard : ProgHOL 64:=.ite (.cmp .equal (localVar "len") (.const 0#64)) (.raise (ofString "TxErr") (.const 1#64)) .skip
def listGuard : ProgHOL 64:=TransactionFields.rejectUnequal (.rfield 0 (localVar "top")) (.const 1#64) 3#64

theorem empty_shape : body=.seq emptyGuard afterEmpty := by
  simp only [body,emptyGuard,afterEmpty,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

/-- Nonempty input is derived from the actual preceding guard, including
cases where its exception shape is missing or malformed. -/
theorem nonempty_of_guard (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (normal : evaluateHOLFiniteState source emptyGuard=(none,target)) : 1≤length.toNat := by
  by_contra empty
  have zero : length=0#64:=BitVec.eq_of_toNat_eq (by change length.toNat=0; omega)
  have read : eval source (.cmp .equal (localVar "len") (.const 0#64))=some (.val (.word 1#64)):=by
    simp [eval,evalHOLExact,toExact,localVar,lengthCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [emptyGuard,evaluateHOLFiniteState_ite] at normal
  simp only [eval] at read
  rw [read] at normal
  exact raise_ne_none source (ofString "TxErr") (.const 1#64) (congrArg Prod.fst normal)

/-- The real reached list guard establishes a list payload contained in
its complete selected input. No payload or later conversion is assumed. -/
theorem payload_of_guard (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) (answer : ValueHOL 64)
    (complete : Rlp.Decode.Complete pointer length answer) (fits : pointer.toNat+length.toNat<2^64)
    (topCell : source.locals.lookup (ofString "top")=some answer)
    (normal : evaluateHOLFiniteState source listGuard=(none,target)) :
    ∃ header payload,answer=Rlp.Item.result pointer header payload 1#64 ∧ 1≤header.toNat ∧
      (pointer+header).toNat=pointer.toNat+header.toNat ∧ (pointer+header).toNat+payload.toNat=pointer.toNat+length.toNat ∧
      payload.toNat≤length.toNat ∧
      evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
        [.rfield 1 (localVar "top"),.rfield 2 (localVar "top")]=some (Rlp.Header.values (pointer+header) payload) := by
  obtain ⟨header,payload,flag,same,small,positive,total,binary,listHeader⟩:=complete
  have tagRead : eval source (.rfield 0 (localVar "top"))=some (.val (.word flag)):=by
    simp [eval,evalHOLExact,toExact,localVar,topCell,same,Rlp.Item.result]
  have flagEq:=TransactionFields.reject_unequal_normal source target (.rfield 0 (localVar "top")) (.const 1#64) 3#64 flag 1#64 tagRead rfl normal
  subst flag
  have added : (pointer+header).toNat=pointer.toNat+header.toNat:=BitVec.toNat_add_of_lt (by omega)
  refine ⟨header,payload,same,listHeader rfl,added,by omega,by omega,?_⟩
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,topCell,same,Rlp.Item.result,Rlp.Header.values]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_transaction_rlp")=some ([(ofString "p",.one),(ofString "len",.one)],body,.one) := by
  have checked:=OriginalCode.indexed code installed 279 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_decode_transaction_rlp) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.Software.guestFn_decode_transaction_rlp,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked


def afterTypeStore : ProgHOL 64:=match afterSelection with | .seq _ rest=>rest | _=>.skip
def afterListGuard : ProgHOL 64:=match afterTypeStore with | .seq _ rest=>rest | _=>.skip
def afterSlices : ProgHOL 64:=match afterListGuard with | .decCall _ _ _ _ rest=>rest | _=>.skip
def sliceArguments : List (ExpHOL 64):=[.rfield 1 (localVar "top"),.rfield 2 (localVar "top")]

set_option maxRecDepth 100000 in
theorem continuation_shapes : afterSelection=.seq (.store (.op .add [localVar "tx",.const 0#64]) (localVar "t")) afterTypeStore ∧
    afterTypeStore=.seq listGuard afterListGuard ∧
    afterListGuard=.decCall (ofString "lst") Rlp.Slices.resultShape (ofString "rlp_list_to_slices") sliceArguments afterSlices := by
  simp (maxSteps:=1000000) only [afterTypeStore,afterListGuard,afterSlices,afterSelection,listGuard,TransactionFields.rejectUnequal,
    selectionAndFields,afterType,afterTop,envelopeDeclarations,afterRawPointer,afterZero,afterAllocation,afterByte,afterEmpty,body,
    sliceArguments,Rlp.Slices.resultShape,Guest.Software.guestFn_decode_transaction_rlp,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]
  trivial

theorem decode_call_no_return (typed : Bool) : NoReturn.Never (decodeCall typed) := by
  have safe : LocalPrefix (ofString "p") (decodeCall typed):=by
    unfold decodeCall
    exact .call (some (ofString "top")) _ _ (by intro name same; cases same; decide)
  intro F source value
  exact (safe.summary source).2 value

theorem selection_no_return : NoReturn.Never selection := by
  rw [selection_shapes.2.1]
  apply NoReturn.conditional
  · rw [selection_shapes.2.2.1]
    apply NoReturn.sequence _ _ (decode_call_no_return true)
    intro F source value
    exact ((updates_saved (ofString "p") (by decide) (by decide)).summary source).2 value
  · rw [selection_shapes.2.2.2]
    exact NoReturn.conditional _ _ _ (decode_call_no_return false) (NoReturn.raise _ _)

/-- The later field suffix is charged only after the same actual selector
returns a complete parse. Rejections, malformed reads and short clocks stay
in the selector's all-outcome allowance. -/
theorem fields_reached_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length) (tailPrice : Nat)
    (tail : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,∀ typed : Bool,∀ answer,
      Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer→
      current.locals.lookup (ofString "top")=some answer→Rlp.CurrentItem.Frame source current→
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=source.locals.lookup key)→
      current.clock-(evaluateHOLFiniteState current afterSelection).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source selectionAndFields).2.clock≤60*length.toNat+13+tailPrice := by
  rw [selection_shapes.1]
  apply ClockCost.sequence_reached_current source selection afterSelection (60*length.toNat+13) tailPrice (selection_cost source pointer length entry)
  intro current normal
  obtain ⟨typed,answer,complete,topCell,frame,saved⟩:=selection_normal source current pointer length entry normal
  exact tail current typed answer complete topCell frame saved

/-- A genuine enclosing return reaches the real field continuation with
its observed parse and memory frame; no future normal return is postulated. -/
theorem fields_returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (entry : Rlp.CurrentItem.Entry source pointer length) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source selectionAndFields=(some (.returned value),target)) :
    ∃ current,∃ typed : Bool,∃ answer,Rlp.Decode.Complete (if typed then pointer+1#64 else pointer) (if typed then length-1#64 else length) answer ∧
      current.locals.lookup (ofString "top")=some answer ∧ Rlp.CurrentItem.Frame source current ∧
      (∀ key,key≠ofString "top"→key≠ofString "t"→key≠ofString "nfields"→current.locals.lookup key=source.locals.lookup key) ∧
      evaluateHOLFiniteState current afterSelection=(some (.returned value),target) := by
  rw [selection_shapes.1] at normal
  obtain ⟨current,selected,continued⟩:=sequence_returned source target selection afterSelection value (selection_no_return source) normal
  obtain ⟨typed,answer,complete,topCell,frame,saved⟩:=selection_normal source current pointer length entry selected
  exact ⟨current,typed,answer,complete,topCell,frame,saved,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.updates_saved
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.updates_readonly
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.updates_quiet
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.typed_extent
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_call_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.empty_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.nonempty_of_guard
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.payload_of_guard
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.original_code

#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.continuation_shapes
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.decode_call_no_return
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.selection_no_return
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_reached_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.TransactionEnvelope.fields_returned
