import InitECandidate.Solver.Input.CurrentVerify.TransactionFields
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
      PersistentNormalFrame source current heap→current.clock-(evaluateHOLFiniteState current (fields kind)).2.clock≤price) :
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
      exact after_conversion_cost kind rows price (fun arity=>tail _ _ _ _ rows arity continued))
  omega

/-- Complete actual parse/conversion/shape prefix of either nested entry.
Only the real checked field state is supplied to its remaining-work price. -/
theorem iteration_prefix_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer length heap : BitVec 64}
    (kind : Kind) (entry : Entry source pointer length heap) (price : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rowArguments=some (Rlp.Header.values pointer length))
    (tail : ∀ current payloadPointer payloadLength next count items,
      payloadPointer.toNat+payloadLength.toNat≤pointer.toNat+length.toNat→payloadLength.toNat≤length.toNat→
      Rows current payloadPointer payloadLength heap next count items→count=expected kind→
      PersistentNormalFrame source current heap→current.clock-(evaluateHOLFiniteState current (fields kind)).2.clock≤price) :
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
      intro current next count items rows arity converted
      exact tail current (pointer+header) payload next count items contained payloadBound rows arity
        (parseFrame.trans source ready current heap heap converted (Nat.le_refl _)))
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
