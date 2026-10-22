import InitECandidate.Solver.Input.PayloadHeaderCleared

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def headerAddress (offset : Nat) : ExpHOL 64:=.op .add [localVar "h",.const (BitVec.ofNat 64 offset)]
def markHeader : ProgHOL 64:=.store (headerAddress 0) (.const 1#64)
def storeParent : ProgHOL 64:=.store (headerAddress 8) (.op .add [localVar "raw",.const 0#64])
def afterFirstStores : List CallPrefix.Action:=afterClear.drop 2
def markedHeader (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let cleared:=clearedHeader input source heap
  {cleared with memory:=StoreWord.put cleared.memory heap 1#64}
def parentStoredHeader (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let marked:=markedHeader input source heap
  {marked with memory:=StoreWord.put marked.memory (heap+8#64) (inputPointer+62#64)}

set_option maxRecDepth 100000 in
theorem first_store_actions : afterClear=.command markHeader::.command storeParent::afterFirstStores := by
  simp only [afterClear,afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterFirstStores,markHeader,storeParent,headerAddress,localVar]
  rfl

theorem mark_execute (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0) :
    evaluateHOLFiniteState (clearedHeader input source heap) markHeader=(none,markedHeader input source heap) := by
  let cleared:=clearedHeader input source heap
  have hCell : cleared.locals.lookup (ofString "h")=some (.val (.word heap)):=by
    simp [cleared,clearedHeader,allocatedHeader,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have address : eval cleared (headerAddress 0)=some (.val (.word heap)):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerAddress,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped : cleared.memaddrs heap:=by
    simpa [byteAddress] using AllocatedBytes.word_mapped cleared heap 248 0 domain arena (by decide) aligned (by decide)
  exact StoreWord.execute cleared (headerAddress 0) (.const 1#64) heap 1#64 address rfl mapped

theorem parent_execute (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0) :
    evaluateHOLFiniteState (markedHeader input source heap) storeParent=(none,parentStoredHeader input source heap) := by
  let marked:=markedHeader input source heap
  have hCell : marked.locals.lookup (ofString "h")=some (.val (.word heap)):=by
    simp [marked,markedHeader,clearedHeader,allocatedHeader,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have rawCell : marked.locals.lookup (ofString "raw")=some (.val (.word (inputPointer+62#64))):=by
    simp [marked,markedHeader,clearedHeader,allocatedHeader,readEntry,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,
      HolFiniteMapExact.update,FUPDATE,show ofString "h"≠ofString "raw" from by decide]
  have address : eval marked (headerAddress 8)=some (.val (.word (heap+8#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,headerAddress,localVar,hCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have value : eval marked (.op .add [localVar "raw",.const 0#64])=some (.val (.word (inputPointer+62#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,rawCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have mapped : marked.memaddrs (heap+8#64):=
    AllocatedBytes.word_mapped marked heap 248 8 domain arena (by decide) aligned (by decide)
  exact StoreWord.execute marked (headerAddress 8) (.op .add [localVar "raw",.const 0#64]) (heap+8#64) (inputPointer+62#64) address value mapped

theorem stores_from_execution (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (execution : CallPrefix.Execution (clearedHeader input source heap) afterClear current) :
    CallPrefix.Execution (parentStoredHeader input source heap) afterFirstStores current := by
  rw [first_store_actions] at execution
  have marked:=execution.command_known markHeader _ (mark_execute input source heap domain arena aligned)
  exact marked.command_known storeParent afterFirstStores (parent_execute input source heap domain arena aligned)

theorem first_stores (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 248 ∧ heap.toNat%8=0 ∧ workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧
      CallPrefix.Execution (parentStoredHeader input source heap) afterFirstStores current := by
  obtain ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,next⟩:=clearing input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  exact ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,stores_from_execution input source current heap ready.environment.domain arena aligned next⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.first_store_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.mark_execute
#print axioms InitECandidate.Solver.Input.PayloadHeader.parent_execute
#print axioms InitECandidate.Solver.Input.PayloadHeader.stores_from_execution
#print axioms InitECandidate.Solver.Input.PayloadHeader.first_stores
