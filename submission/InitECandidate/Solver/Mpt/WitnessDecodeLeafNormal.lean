import InitECandidate.Solver.Mpt.WitnessDecodeRecordProgram
import InitECandidate.Solver.Mpt.NodeConstructorNormal
import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def leafWords (nibbles nibbleLength valuePointer valueLength : BitVec 64) : String→BitVec 64
  | "nib"=>nibbles | "nlen"=>nibbleLength | "vptr"=>valuePointer | "vlen"=>valueLength | _=>0#64
def leafParentWords (pointer length : BitVec 64) : String→BitVec 64
  | "p"=>pointer | "n"=>length | _=>0#64
def leafAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  {PersistentAlloc.post {source with clock:=source.clock-2} heap 64#64 with
    memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf words))}

/-- Original leaf allocation and its parent-encoding metadata stores return
the genuine fresh64-byte node. Its constructor data, all metadata writes,
unchanged scratch arena and actual two caller ticks are derived from the run. -/
theorem leaf_allocation_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length nibbles nibbleLength leaf valueFlag valuePointer valueLength valueTotal heap cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (valueCell : source.locals.lookup (ofString "vi")=some (.rStruct [.val (.word valueFlag),.val (.word valuePointer),.val (.word valueLength),.val (.word valueTotal)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source leafAllocate=(some (.returned value),target)) :
    AllocatedBytes.Arena heap 64 ∧ Rlp.Validation.Arena target cursor limit ∧
      value=.rStruct [.val (.word 0#64),.val (.word heap)] ∧ 2≤source.clock ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {leafAllocated source heap (leafWords nibbles nibbleLength valuePointer valueLength) with
          memory:=WordWrites.write (leafAllocated source heap (leafWords nibbles nibbleLength valuePointer valueLength)).memory
            (LocalFields.writes heap (leafFields (leafParentWords pointer length)))} := by
  let words:=leafWords nibbles nibbleLength valuePointer valueLength
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [field "cn" 0,field "cn" 1,field "vi" 1,field "vi" 2]=
      some [.val (.word nibbles),.val (.word nibbleLength),.val (.word valuePointer),.val (.word valueLength)]:=by
    simp [field,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,compactCell,valueCell]
  obtain ⟨callee,called,nibCell,nlenCell,vptrCell,vlenCell⟩:=Input.word_quad_environment source.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (NodeConstructor.body .leaf) .one nibbles nibbleLength valuePointer valueLength
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (NodeConstructor.original_code .leaf source.code installed)
  rw [leaf_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source target "lf" .one (ofString "node_new_leaf") _ _
    (NodeConstructor.body .leaf) afterLeaf callee .one args called value normal
  have inputs : NodeConstructor.Inputs .leaf (callEntryStateHOLFinite source callee) words:=⟨nibCell,nlenCell,vptrCell,vlenCell⟩
  obtain ⟨returnedEq,nodeArena,nodeFunding,nodeFrame⟩:=NodeConstructor.scalar_normal .leaf (by decide) (callEntryStateHOLFinite source callee) built heap words
    inputs arena.domain heapCell heapArena heapAligned installed returned bodyRun
  change AllocatedBytes.Arena heap 64 at nodeArena
  rw [returnedEq] at continued
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) nodeFrame
  change {built with locals:=source.locals}=
    {PersistentAlloc.post {source with clock:=source.clock-1-1} heap 64#64 with memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf words))} at callerFrame
  rw [Nat.sub_sub] at callerFrame
  change {built with locals:=source.locals}=leafAllocated source heap words at callerFrame
  let ready:=bind (leafAllocated source heap words) "lf" heap
  change evaluateHOLFiniteState (bind {built with locals:=source.locals} "lf" heap) afterLeaf=(some (.returned value),inner) at continued
  rw [callerFrame] at continued
  have node : ready.locals.lookup (ofString "lf")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (bind_lookup_other (leafAllocated source heap words) "lf" "p" heap (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other (leafAllocated source heap words) "lf" "n" heap (by decide)).trans lengthCell
  have fieldsReady : ∀ field∈leafFields (leafParentWords pointer length),field.value.Ready ready:=by
    simp [leafFields,leafParentWords,LocalFields.Operand.Ready,currentPointer,currentLength]
  have mapped : ∀ field∈leafFields (leafParentWords pointer length),ready.memaddrs (heap+BitVec.ofNat 64 field.offset):=by
    intro field member
    have geometry:=leaf_geometry (leafParentWords pointer length) field member
    exact AllocatedBytes.word_mapped ready heap 64 field.offset arena.domain nodeArena (by omega) heapAligned geometry.2
  rw [leaf_tail_shape (leafParentWords pointer length),LocalFields.execute ready "lf" heap _ node fieldsReady mapped] at continued
  obtain ⟨read,innerEq⟩:=Input.return_normal _ inner (.rstruct [.const 0#64,localVar "lf"]) value continued
  have expected : eval {ready with memory:=WordWrites.write ready.memory (LocalFields.writes heap (leafFields (leafParentWords pointer length)))}
      (.rstruct [.const 0#64,localVar "lf"])=some (.rStruct [.val (.word 0#64),.val (.word heap)]):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,node]
  have valueEq:=Option.some.inj (read.symm.trans expected)
  have finalFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source heap words with
        memory:=WordWrites.write (leafAllocated source heap words).memory
          (LocalFields.writes heap (leafFields (leafParentWords pointer length)))}:=by
    rw [endpoint,innerEq]
    rfl
  have globals:=congrArg PanSemStateFiniteExact.globals finalFrame
  change target.globals=(PersistentAlloc.post source heap 64#64).globals at globals
  have domain:=congrArg PanSemStateFiniteExact.memaddrs finalFrame
  change target.memaddrs=source.memaddrs at domain
  have finalArena : Rlp.Validation.Arena target cursor limit:=by
    refine ⟨domain.trans arena.domain,?_,?_,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
    · rw [globals]
      simpa [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.cursorGlobal
    · rw [globals]
      simpa [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal
  change 1≤source.clock-1 at nodeFunding
  exact ⟨nodeArena,finalArena,valueEq,by omega,finalFrame⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_allocation_normal
