import InitECandidate.Solver.Mpt.WitnessResolveProgram
import InitECandidate.Solver.Mpt.NodeConstructorNormal
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.WordEnvironment
import InitECandidate.Solver.Rlp.ItemProgram

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def hashWords (hash : BitVec 64) : String→BitVec 64:=fun _=>hash
def hashAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  {PersistentAlloc.post {source with clock:=source.clock-2} heap 32#64 with
    memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .hashed (hashWords hash)))}

/-- A genuine missing-preimage resolver allocation returns its actual
fresh32-byte hashed node, with the exact original constructor stores and
heap update. Allocation room and two caller ticks follow from the run. -/
theorem hash_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag heap : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source hashCall=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)] ∧
      AllocatedBytes.Arena heap 32 ∧ 2≤source.clock ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite (hashAllocated source heap (pointer+header)) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [field "it" 1]=
      some [.val (.word (pointer+header))]:=by
    simp [field,Rlp.Item.result,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,itemCell]
  obtain ⟨callee,called,hashCell⟩:=Input.word_environment source.code.lookup (ofString "node_new_hashed") (ofString "hash")
    (NodeConstructor.body .hashed) .one (pointer+header) (NodeConstructor.original_code .hashed source.code installed)
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post "hn" .one (ofString "node_new_hashed") _ _
    (NodeConstructor.body .hashed) hashReturn callee .one args called value normal
  have inputs : NodeConstructor.Inputs .hashed (callEntryStateHOLFinite source callee) (hashWords (pointer+header)):=hashCell
  obtain ⟨returnedEq,nodeArena,nodeFunding,nodeFrame⟩:=NodeConstructor.scalar_normal .hashed (by decide) (callEntryStateHOLFinite source callee) built heap (hashWords (pointer+header))
    inputs domain heapCell arena aligned installed returned bodyRun
  rw [returnedEq] at continued
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) nodeFrame
  change {built with locals:=source.locals}=
    {PersistentAlloc.post {source with clock:=source.clock-1-1} heap 32#64 with
      memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .hashed (hashWords (pointer+header))))} at callerFrame
  rw [Nat.sub_sub] at callerFrame
  change {built with locals:=source.locals}=hashAllocated source heap (pointer+header) at callerFrame
  let ready:=bind (hashAllocated source heap (pointer+header)) "hn" heap
  change evaluateHOLFiniteState (bind {built with locals:=source.locals} "hn" heap) hashReturn=(some (.returned value),inner) at continued
  rw [callerFrame] at continued
  have node : ready.locals.lookup (ofString "hn")=some (.val (.word heap)):=bind_lookup_same _ _ _
  obtain ⟨read,innerEq⟩:=Input.return_normal ready inner _ value continued
  have expected : eval ready (.rstruct [.const 0#64,localVar "hn",.const 0#64,.const 0#64])=
      some (.rStruct [.val (.word 0#64),.val (.word heap),.val (.word 0#64),.val (.word 0#64)]):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,node]
  have valueEq:=Option.some.inj (read.symm.trans expected)
  refine ⟨valueEq,nodeArena,?_,?_⟩
  · change 1≤source.clock-1 at nodeFunding
    omega
  · rw [endpoint,innerEq]
    rfl

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_call_normal
