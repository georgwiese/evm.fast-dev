import InitECandidate.Solver.Mpt.NodeBranchConstructor
import InitECandidate.Solver.WitnessRadix.ZeroNormal

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual normal branch construction derives its fresh 176-byte arena,
returns the old heap word and initializes exactly the real zeroed branch
with kind3. Both allocation and zeroing funding come from the real run. -/
theorem branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .branch)=(some (.returned value),target)) :
    value=.val (.word heap) ∧ AllocatedBytes.Arena heap 176 ∧ 9≤source.clock ∧
    emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {PersistentAlloc.post {source with clock:=source.clock-9} heap 176#64 with
        memory:=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64} := by
  rw [allocation_shape] at normal
  obtain ⟨room,positive,inner,tailRun,endpoint⟩:=PersistentAlloc.call_normal source target "nd" [.const 176#64] (tail .branch) heap 176#64 rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=arena.upper; omega) value normal
  have nodeArena : AllocatedBytes.Arena heap 176:=⟨arena.lower,room⟩
  let ready:=QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 176#64) "nd" heap
  have node : ready.locals.lookup (ofString "nd")=some (.val (.word heap)):=QueryBranch.bind_lookup_same _ _ _
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) branchArguments=some (Zero.values heap 176):=by
    simp [branchArguments,Zero.values,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,node]
  rw [branch_tail_shape] at tailRun
  have prefixSafe : Input.LocalPrefix (ofString "nd") branchZero:=.call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,zeroRun,footerRun,localFrame⟩:=prefixSafe.normal_continue ready inner branchFooter value tailRun
  obtain ⟨funded,zeroEq⟩:=Zero.call_normal ready middle branchArguments heap 176 args (Zero.original_code source.code installed) (by decide) (by decide) aligned
    (fun offset inside offsetAligned=>AllocatedBytes.word_mapped ready heap 176 offset domain nodeArena (by omega) aligned offsetAligned) zeroRun
  change 8≤source.clock-1 at funded
  let zeroed:={ready with memory:=Zero.finalMemory ready.memory heap 176,clock:=ready.clock-8}
  have middleEq : middle=zeroed:=zeroEq
  rw [middleEq] at footerRun
  have currentNode : zeroed.locals.lookup (ofString "nd")=some (.val (.word heap)):=node
  have mapped : zeroed.memaddrs heap:=by
    simpa only [byteAddress,BitVec.add_zero] using
      AllocatedBytes.word_mapped zeroed heap 176 0 domain nodeArena (by decide) aligned (by decide)
  have stored:=FieldStores.execute zeroed "nd" "" heap 0#64 branchFields currentNode
    (by simp [branchFields,FieldStores.Value.Ready]) (by simpa [branchFields] using mapped)
    (by simp [branchFields,FieldStores.Value.Avoid]) (.return (QueryBranch.localVar "nd"))
  change evaluateHOLFiniteState zeroed (FieldStores.program "nd" "" branchFields (.return (QueryBranch.localVar "nd")))=(some (.returned value),inner) at footerRun
  rw [stored] at footerRun
  obtain ⟨read,innerEq⟩:=Input.return_normal _ inner (QueryBranch.localVar "nd") value footerRun
  have expected : QueryBranch.eval {zeroed with memory:=WordWrites.write zeroed.memory (FieldStores.writes heap branchFields)}
      (QueryBranch.localVar "nd")=some (.val (.word heap)):=by
    simp [QueryBranch.eval,QueryBranch.localVar,evalHOLExact,toExact,currentNode]
  have valueEq : value=.val (.word heap):=Option.some.inj (read.symm.trans expected)
  refine ⟨valueEq,nodeArena,by omega,?_⟩
  rw [endpoint,innerEq]
  simp only [FieldStores.writes,branchFields,List.map_cons,List.map_nil,WordWrites.write,BitVec.add_zero]
  change emptyLocalsHOLFinite {PersistentAlloc.post {source with clock:=source.clock-1-8} heap 176#64 with
    memory:=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64}= _
  rw [Nat.sub_sub]

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_normal
