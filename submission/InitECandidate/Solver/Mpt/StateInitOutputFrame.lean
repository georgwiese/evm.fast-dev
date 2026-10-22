import InitECandidate.Solver.Mpt.StateInitInputFrame

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessCore

/-- Pure caller checks may change locals and spend loop ticks. They retain
the complete initialized trie, tables, journal and older input agreement. -/
theorem Output.of_erase (input : Guest.InputBlob) (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (output : Output input origin source workspace nodes rootHash codes)
    (same : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Output input origin target workspace nodes rootHash codes := by
  have memory:=Input.LocalEffects.memory_of_erase source target same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  have codeEq:=congrArg PanSemStateFiniteExact.code same
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs same
  have endianEq:=congrArg PanSemStateFiniteExact.be same
  have oracleEq:=congrArg (fun state=>state.ffi.oracle) same
  change target.globals=source.globals at globals
  change target.code=source.code at codeEq
  change target.memaddrs=source.memaddrs at domainEq
  change target.be=source.be at endianEq
  change target.ffi.oracle=source.ffi.oracle at oracleEq
  obtain ⟨installed,scalars,scratch,otherGlobals,code,domain,endian,oracle,heap,root,storage,heapCell,arena,aligned,view,frozen,table,bs,
    registry,member,regions,block,older⟩:=output
  have nextScratch:=scratch.of_fields source target 2713714688#64 2701135872#64 domainEq globals
  have nextView : WorkspaceView target workspace nodes rootHash codes root storage:=by
    refine ⟨view.arena,view.aligned,?_,?_,?_,?_,?_,?_⟩
    · rw [globals]; exact view.pointer
    all_goals rw [memory]
    · exact view.nodeDatabase
    · exact view.rootHash
    · exact view.codeDatabase
    · exact view.root
    · exact view.storageTable
  have nextFrozen:=frozen.frame input (QueryBranch.bind source "db" nodes) (QueryBranch.bind target "db" nodes) workspace.toNat domainEq endianEq
    ((bind_lookup_same target "db" nodes).trans (bind_lookup_same source "db" nodes).symm)
    (by intro query lower upper; exact congrFun memory query)
  obtain ⟨next,sameNodes⟩:=registry.of_fields source target (PersistentAlloc.rounded workspace 40#64).toNat heap nodes memory domainEq
  have nextMember : next.graph.valid root:=by rw [sameNodes]; exact member
  have nextRegions:=regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph
    (PersistentAlloc.rounded workspace 40#64).toNat storage.toNat sameNodes (by intro node known active; rw [memory])
  have nextTable:=TableState.of_fields table globals memory domainEq endianEq
  have nextBlock:=block.of_fields source target (BitVec.ofNat 64 (NaturalLayout.freshEnd .word storage.toNat 64)) workspace globals memory domainEq endianEq
  refine ⟨by rw [codeEq]; exact installed,by rw [globals]; exact scalars,nextScratch,?_,codeEq.trans code,domainEq.trans domain,
    endianEq.trans endian,oracleEq.trans oracle,heap,root,storage,?_,arena,aligned,nextView,nextFrozen,nextTable,?_,next,nextMember,nextRegions,nextBlock,?_⟩
  · intro key h w b s c j n t
    rw [globals]
    exact otherGlobals key h w b s c j n t
  · rw [globals]; exact heapCell
  · rw [globals]; exact bs
  · intro query lower upper
    exact (congrFun memory query).trans (older query lower upper)

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.Output.of_erase
