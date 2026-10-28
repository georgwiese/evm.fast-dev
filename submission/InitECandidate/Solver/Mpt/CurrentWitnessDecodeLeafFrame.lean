import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeaf
import InitECandidate.Solver.Mpt.CurrentNodeConstructorFrame
import InitECandidate.Solver.Input.WordQuadEnvironment
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The two real parent-encoding stores stay inside their genuine fresh
node, preserving earlier words and every nonmemory runtime field. -/
theorem current_after_leaf_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer length frontier : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "lf")=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (allocation : AllocatedBytes.Arena node 64)
    (aligned : node.toNat%8=0) (fresh : frontier.toNat≤node.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word node)] ∧ MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,query.toNat<frontier.toNat→post.memory query=source.memory query := by
  let one : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (node+8#64) pointer}
  let two : PanSemStateFiniteExact 64 Guest.HostMemory:={one with memory:=StoreWord.put one.memory (node+16#64) length}
  have address (current : PanSemStateFiniteExact 64 Guest.HostMemory) (offset : BitVec 64)
      (cell : current.locals.lookup (ofString "lf")=some (.val (.word node))) :
      eval current (.op .add [localVar "lf",.const offset])=some (.val (.word (node+offset))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have pRead : eval source (localVar "p")=some (.val (.word pointer)):=by simp [eval,evalHOLExact,localVar,toExact,pointerCell]
  have nRead : eval one (localVar "n")=some (.val (.word length)):=by simp [eval,evalHOLExact,localVar,toExact,one,lengthCell]
  have first:=StoreWord.execute source (.op .add [localVar "lf",.const 8#64]) (localVar "p") (node+8#64) pointer
    (address source 8#64 nodeCell) pRead (AllocatedBytes.word_mapped source node 64 8 domain allocation (by decide) aligned (by decide))
  have second:=StoreWord.execute one (.op .add [localVar "lf",.const 16#64]) (localVar "n") (node+16#64) length
    (address one 16#64 nodeCell) nRead (AllocatedBytes.word_mapped one node 64 16 domain allocation (by decide) aligned (by decide))
  have finish : evaluateHOLFiniteState two (.return (.rstruct [.const 0#64,localVar "lf"]))=
      (some (.returned (.rStruct [.val (.word 0#64),.val (.word node)])),emptyLocalsHOLFinite two) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,localVar,toExact,two,one,nodeCell,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [after_leaf_shape,StateSteps.next_sequence source one _ _ first (Nat.le_refl _),StateSteps.next_sequence one two _ _ second (Nat.le_refl _),finish] at normal
  have valueEq : value=.rStruct [.val (.word 0#64),.val (.word node)] := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst normal).symm
  have endpoint : post=emptyLocalsHOLFinite two:=(congrArg Prod.snd normal).symm
  refine ⟨valueEq,by rw [endpoint]; rfl,?_⟩
  intro query before
  have away (offset : Nat) (small : offset<64) : query≠node+BitVec.ofNat 64 offset := by
    have number:=byteAddress_toNat node offset (by have upper:=allocation.upper; omega)
    intro same
    have observed:=congrArg BitVec.toNat same
    change query.toNat=(byteAddress node offset).toNat at observed
    rw [number] at observed
    omega
  rw [endpoint]
  change StoreWord.put (StoreWord.put source.memory (node+8#64) pointer) (node+16#64) length query=source.memory query
  simp only [StoreWord.put,if_neg (away 16 (by decide)),if_neg (away 8 (by decide))]

def currentLeafWords (nibbles nibbleLength valuePointer valueLength : BitVec 64) : String→BitVec 64
  | "nib"=>nibbles | "nlen"=>nibbleLength | "vptr"=>valuePointer | "vlen"=>valueLength | _=>0#64

/-- Connect the real leaf constructor return and the original two stores
to the same caller's complete persistent frame. -/
theorem current_leaf_allocate_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length nibbles nibbleLength leaf valueFlag valuePointer valueLength valueTotal heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (valueCell : source.locals.lookup (ofString "vi")=some (.rStruct [.val (.word valueFlag),.val (.word valuePointer),.val (.word valueLength),.val (.word valueTotal)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source leafAllocate=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word heap)] ∧ PersistentNormalFrame source post heap := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [field "cn" 0,field "cn" 1,field "vi" 1,field "vi" 2]=some [.val (.word nibbles),.val (.word nibbleLength),.val (.word valuePointer),.val (.word valueLength)] := by
    simp [field,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,compactCell,valueCell]
  obtain ⟨callee,called,nibCell,nlenCell,vptrCell,vlenCell⟩:=word_quad_environment source.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (NodeConstructor.body .leaf) .one
    nibbles nibbleLength valuePointer valueLength (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (NodeConstructor.original_code .leaf source.code arena.code)
  rw [leaf_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "lf" .one (ofString "node_new_leaf") _ _
    (NodeConstructor.body .leaf) afterLeaf callee .one args called value normal
  have inputs : NodeConstructor.Inputs .leaf (callEntryStateHOLFinite source callee) (currentLeafWords nibbles nibbleLength valuePointer valueLength):=⟨nibCell,nlenCell,vptrCell,vlenCell⟩
  obtain ⟨returnedEq,nodeArena,frame⟩:=NodeConstructor.scalar_persistent_frame .leaf (by decide) (callEntryStateHOLFinite source callee) built heap _ inputs arena.domain
    heapCell heapArena heapBound aligned arena.code returned bodyRun
  rw [returnedEq] at continued
  let ready:=CallNormal.continuationEntry source built "lf" (.val (.word heap))
  have callerFrame : PersistentNormalFrame source ready heap:=frame.of_erase _ _ source ready heap rfl rfl
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (CallNormal.continuation_lookup_other source built "lf" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word length)):=
    (CallNormal.continuation_lookup_other source built "lf" "n" _ (by decide)).trans lengthCell
  obtain ⟨valueEq,runtime,memory⟩:=current_after_leaf_frame ready inner heap pointer length heap (CallNormal.continuation_lookup_same _ _ _ _)
    currentPointer currentLength (callerFrame.current_arena arena).domain nodeArena aligned (Nat.le_refl _) value continued
  have innerFrame:=callerFrame.after_memory source ready inner heap runtime memory
  exact ⟨valueEq,innerFrame.of_erase source inner source post heap rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_after_leaf_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_leaf_allocate_frame
