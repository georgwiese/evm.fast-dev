import InitECandidate.Solver.Mpt.NewProgram
import InitECandidate.Solver.WitnessRadix.AllocationNoWrapTrace
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.NewTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 16#64) "m" heap
def rootStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root : BitVec 64):=
  let before:=allocated source heap
  {before with memory:=StoreWord.put before.memory heap root}
def ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64):=
  let before:=rootStored source heap root
  {before with memory:=StoreWord.put before.memory (heap+8#64) secured}

theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root_node")=some (.val (.word root)))
    (securedCell : source.locals.lookup (ofString "secured")=some (.val (.word secured)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 16) (aligned : heap.toNat%8=0) :
    evaluateHOLFiniteState (allocated source heap) tail=(some (.returned (.val (.word heap))),emptyLocalsHOLFinite (ready source heap root secured)) := by
  let entry:=allocated source heap
  have mCell : entry.locals.lookup (ofString "m")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have rootLocal : entry.locals.lookup (ofString "root_node")=some (.val (.word root)):=
    (bind_lookup_other _ "m" "root_node" heap (by decide)).trans rootCell
  have securedLocal : (rootStored source heap root).locals.lookup (ofString "secured")=some (.val (.word secured)):=
    (bind_lookup_other _ "m" "secured" heap (by decide)).trans securedCell
  have address0 : eval entry (address 0)=some (.val (.word heap)):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,address,localVar,mCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rootRead : eval entry (localVar "root_node")=some (.val (.word root)):=by simp [eval,evalHOLExact,toExact,localVar,rootLocal]
  have first:=StoreWord.execute entry (address 0) (localVar "root_node") heap root address0 rootRead
    (by simpa [byteAddress] using AllocatedBytes.word_mapped entry heap 16 0 domain arena (by decide) aligned (by decide))
  have nextM : (rootStored source heap root).locals.lookup (ofString "m")=some (.val (.word heap)):=mCell
  have address8 : eval (rootStored source heap root) (address 8)=some (.val (.word (heap+8#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,address,localVar,nextM,valueIsWord,valueWord,wordOpHOL,wordOp]
  have securedRead : eval (rootStored source heap root) (localVar "secured")=some (.val (.word secured)):=by
    simp [eval,evalHOLExact,toExact,localVar,securedLocal]
  have second:=StoreWord.execute (rootStored source heap root) (address 8) (localVar "secured") (heap+8#64) secured address8 securedRead
    (AllocatedBytes.word_mapped _ heap 16 8 domain arena (by decide) aligned (by decide))
  have finalM : (ready source heap root secured).locals.lookup (ofString "m")=some (.val (.word heap)):=mCell
  have returned : evaluateHOLFiniteState (ready source heap root secured) (.return (localVar "m"))=
      (some (.returned (.val (.word heap))),emptyLocalsHOLFinite (ready source heap root secured)):=by
    simp [evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,finalM,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [tail,storeRoot,storeSecured,StateSteps.next_sequence entry (rootStored source heap root) _ _ first (Nat.le_refl _),
    StateSteps.next_sequence (rootStored source heap root) (ready source heap root secured) _ _ second (Nat.le_refl _),returned]

/-- The actual normal constructor derives its16-byte room, returned
workspace pointer and exact two stored words. Only current heap/input
facts are supplied; no future allocation success or clock allowance is. -/
theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (rootCell : source.locals.lookup (ofString "root_node")=some (.val (.word root)))
    (securedCell : source.locals.lookup (ofString "secured")=some (.val (.word secured)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    AllocatedBytes.Arena heap 16 ∧ value=.val (.word heap) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite (ready source heap root secured) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 16#64]=some (PersistentAlloc.values 16#64):=rfl
  have shaped:=run
  rw [body_shape] at shaped
  obtain ⟨room,funded,inner,continued,endpoint⟩:=PersistentAlloc.call_normal_no_wrap source target "m" [.const 16#64] tail heap 16#64 args
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell
    (by change heap.toNat+16+7<2^64; have upper:=frontier.upper; omega) value shaped
  have arena : AllocatedBytes.Arena heap 16:=⟨frontier.lower,by change heap.toNat+16≤2952790016 at room; omega⟩
  have allocation:=PersistentAlloc.call_execute source "m" [.const 16#64] tail heap 16#64 args
    (PersistentAlloc.original_code source.code installed) heapCell room (by omega)
  have suffix:=tail_execute source heap root secured rootCell securedCell domain arena aligned
  have actual : evaluateHOLFiniteState source body=
      (some (.returned (.val (.word heap))),restore source "m" (emptyLocalsHOLFinite (ready source heap root secured))):=by
    rw [body_shape,allocation]
    change (let output:=evaluateHOLFiniteState (allocated source heap) tail;(output.1,restore source "m" output.2))=_
    rw [suffix]
  have result:=congrArg Prod.fst (run.symm.trans actual)
  have targetEq:=congrArg Prod.snd (run.symm.trans actual)
  change target=restore source "m" (emptyLocalsHOLFinite (ready source heap root secured)) at targetEq
  refine ⟨arena,PanSemResultExact.returned.inj (Option.some.inj result),?_⟩
  rw [targetEq]
  rfl

end InitECandidate.Solver.Mpt.NewTrie

#print axioms InitECandidate.Solver.Mpt.NewTrie.tail_execute
#print axioms InitECandidate.Solver.Mpt.NewTrie.normal
