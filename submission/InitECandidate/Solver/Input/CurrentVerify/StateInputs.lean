import InitECandidate.Solver.Input.CurrentVerify.StateEntry
import InitECandidate.Solver.Input.CurrentVerify.StateCallTrace

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual current state_init entry: matching decoded node/table images,
its real persistent frontier and three typed formal arguments. -/
def StateInitInputs (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si : BitVec 64) (boundary : Nat) : Prop :=
  ∃ array table cap root codes heap start length,
    CurrentStartup.ArenaState source ∧
    CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31) ∧
    CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length) ∧
    source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    2701131776≤heap.toNat ∧ heap.toNat≤2952790016 ∧ heap.toNat%8=0 ∧ boundary≤heap.toNat ∧
    (CurrentTable.New.endPointer table cap).toNat≤heap.toNat ∧
    source.locals.lookup (ofString "nodedb")=some (.val (.word table)) ∧
    source.locals.lookup (ofString "state_root")=some (.val (.word root)) ∧
    source.locals.lookup (ofString "codedb")=some (.val (.word codes)) ∧
    ∃ nodeData : CurrentTable.NodeBuild.Data,CurrentTable.NodeLookup.Database source nodeData ∧
      nodeData.table=table ∧ (CurrentTable.New.endPointer nodeData.table nodeData.cap).toNat≤heap.toNat

/-- All actual state_init arguments and physical entry conditions follow
from main's real database prefix and the observed call. The parent root read
may fail; it is never assumed readable or a valid Ethereum root. -/
theorem RunAttempt.state_init_entry_trace {input : Guest.InputBlob}
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (tables : HasTables input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterCodes=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      StateInitInputs input entry pointer si boundary ∧
      LocalEffects.erase entry=LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      evaluateHOLFiniteState entry Mpt.StateInit.body=(childResult,target) ∧ StateInitResumes source target post childResult outcome := by
  obtain ⟨actualNodeData,actualDatabase,actualNodeCell,actualHeapAfter⟩:=tables.node_database
  obtain ⟨data,payloadLocal,nodeSource,codeSource,array,start,length,codeArray,codeStart,codeLength,table,cap,codes,codeCap,nodeUpper,codeUpper,
    nodeBefore,codeBefore,witness,codeWitness,nodeResult,codeResult,nodeCell,codeCell⟩ := tables
  rcases state_init_call_trace source post table codes data.arena.code nodeCell codeCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨root,entry,target,childResult,rootRead,frame,clock,nodeLocal,rootLocal,codeLocal,bodyRun,resumes⟩ := reached
    obtain ⟨heap,heapCell,heapLower,heapUpper,heapAligned⟩ := data.heap
    obtain ⟨cursor,cursorCell,tableEnd,cursorUpper,cursorAligned⟩ := nodeResult.heap
    have sameHeap : cursor=heap := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using cursorCell.symm.trans heapCell
    rw [sameHeap] at tableEnd
    have memory:=LocalEffects.memory_of_erase source entry frame
    have globals:=congrArg PanSemStateFiniteExact.globals frame
    change entry.globals=source.globals at globals
    have entryWitness:=witness.of_interval (by decide) (by intro query low high; exact congrFun memory query)
    obtain ⟨imageRoot,next,count,valid,bits,left,right,keys,image,countBound⟩ := nodeResult.image
    have entryImage : CurrentTable.NodeBuild.ImageUpTo
        {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} entry (VarList.decodedCount input start length) :=
      ⟨imageRoot,next,count,valid,bits,left,right,keys,image.of_frame frame,countBound⟩
    have sameTable : actualNodeData.table=table:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actualNodeCell.symm.trans nodeCell
    obtain ⟨databaseHeap,databaseHeapCell,databaseEnd,databaseUpper,databaseAligned⟩:=actualHeapAfter
    have sameDatabaseHeap : databaseHeap=heap:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using databaseHeapCell.symm.trans heapCell
    rw [sameDatabaseHeap] at databaseEnd
    have entryDatabase:=actualDatabase.of_frame frame
    have inputs : StateInitInputs input entry pointer si boundary :=
      ⟨array,table,cap,root,codes,heap,start,length,data.arena.of_frame frame,entryWitness,entryImage,
        by rw [globals]; exact heapCell,
        by have h:=data.recordInside; omega,heapUpper,heapAligned,by omega,tableEnd,nodeLocal,rootLocal,codeLocal,actualNodeData,entryDatabase,sameTable,databaseEnd⟩
    exact Or.inr ⟨entry,target,childResult,inputs,frame,clock,bodyRun,resumes⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.state_init_entry_trace
