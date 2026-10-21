import InitECandidate.Solver.Input.RunAttemptWitnessArguments
import InitECandidate.Solver.MutableTable.WitnessDatabase
import InitECandidate.Solver.MutableTable.WitnessDatabaseBeforeLater

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Build := MutableTable.WitnessBuild.Inputs

def codeEntry (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (nodeTable : BitVec 64) :=
  CallNormal.continuationEntry source target "nodedb" (.val (.word nodeTable))

/-- Both unchanged constructor calls are composed using their actual table
returns. The second call's rows, heap room, SI loads and runtime follow from
the first call's genuine output frame and one combined allocation budget. -/
theorem constructors_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (si nodes codes heap stp pad scratch : BitVec 64) (nodeCount codeCount nodeMaximum codeMaximum : Nat)
    (nodeSlices codeSlices : Nat→Graph.Slice)
    (nodeInputs : Build source nodes heap nodeCount nodeMaximum nodeSlices stp pad scratch)
    (codeInputs : Build source codes heap codeCount codeMaximum codeSlices stp pad scratch)
    (room : heap.toNat+72+57*(4*nodeCount+4)+7+72+57*(4*codeCount+4)+7≤33806089496)
    (siArena : AllocatedBytes.Arena si 96) (siAligned : si.toNat%8=0) (siBefore : si.toNat+96≤heap.toNat)
    (buffersBefore : stp.toNat+200≤si.toNat ∧ pad.toNat+136≤si.toNat ∧ scratch.toNat+32≤si.toNat)
    (stateArena : AllocatedBytes.Arena stp 200) (padArena : AllocatedBytes.Arena pad 136) (scratchArena : AllocatedBytes.Arena scratch 32)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (nodePointer : source.memory (byteAddress si 40)=.word nodes)
    (nodeCountCell : source.memory (byteAddress si 48)=.word (BitVec.ofNat 64 nodeCount))
    (codePointer : source.memory (byteAddress si 56)=.word codes)
    (codeCountCell : source.memory (byteAddress si 64)=.word (BitVec.ofNat 64 codeCount))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source constructors=(outcome,post)) :
    source.clock-post.clock≤MutableTable.WitnessBuild.bodyPrice nodeSlices nodeCount+1+MutableTable.WitnessBuild.bodyPrice codeSlices codeCount+1 ∨
      ∃ nodeTarget codeTarget codeTable currentHeap inner,
        MutableTable.WitnessBuild.Returned source nodeTarget nodes heap nodeCount nodeSlices stp pad scratch ∧
        MutableTable.WitnessBuild.Returned (codeEntry source nodeTarget heap) codeTarget codes codeTable codeCount codeSlices stp pad scratch ∧
        MutableTable.WitnessBuild.Database codeTarget nodes heap nodeCount nodeMaximum nodeSlices scratch ∧
        MutableTable.WitnessBuild.Database codeTarget codes codeTable codeCount codeMaximum codeSlices scratch ∧
        codeTarget.globals.lookup (ofString "heap_ptr")=some (.val (.word currentHeap)) ∧
        MutableTable.WitnessBuild.BeforeHeap codeTarget heap currentHeap.toNat ∧
        MutableTable.WitnessBuild.BeforeHeap codeTarget codeTable currentHeap.toNat ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry (codeEntry source nodeTarget heap) codeTarget "codedb" (.val (.word codeTable))) afterCodes=(outcome,inner) ∧
        post=restore source "nodedb" (restore (codeEntry source nodeTarget heap) "codedb" inner) := by
  have nodeArgs:=node_arguments_read source si nodes nodeCount nodeInputs.environment.domain siArena siAligned siCell nodePointer nodeCountCell
  rw [shapes.2.2.2.2.2.2.1] at run
  rcases MutableTable.WitnessBuild.scoped_trace source post nodes heap nodeCount nodeMaximum nodeSlices stp pad scratch nodeInputs "nodedb" nodeArguments afterNodes nodeArgs outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨nodeTarget,first,nodeReturned,continued,endpoint⟩ := reached
    let entry:=codeEntry source nodeTarget heap
    obtain ⟨codeTable,heapLower,heapUpper,nextInputs⟩ := codeInputs.after_build source nodeTarget codes nodes heap codeCount nodeCount codeMaximum codeSlices stp pad scratch nodeReturned.toNormal room
    have actual:=nextInputs.of_fields nodeTarget entry codes codeTable codeCount codeMaximum codeSlices stp pad scratch rfl rfl rfl rfl rfl rfl
    have entrySi : entry.locals.lookup (ofString "si")=some (.val (.word si)) := by
      simp [entry,codeEntry,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      exact siCell
    have frame:=nodeReturned.toNormal.input_frame source nodeTarget nodes heap nodeCount stp pad scratch si.toNat (si.toNat+96) buffersBefore.1 buffersBefore.2.1 buffersBefore.2.2 siBefore
    have memory (offset : Nat) (inside : offset<96) : entry.memory (byteAddress si offset)=source.memory (byteAddress si offset) := by
      have number:=byteAddress_toNat si offset (by have h:=siArena.upper; omega)
      exact frame.words _ (by rw [number]; omega) (by rw [number]; omega)
    have codeArgs:=code_arguments_read entry si codes codeCount actual.environment.domain siArena siAligned entrySi
      ((memory 56 (by decide)).trans codePointer) ((memory 64 (by decide)).trans codeCountCell)
    change evaluateHOLFiniteState entry afterNodes=(outcome,first) at continued
    rw [shapes.2.2.2.2.2.2.2] at continued
    rcases MutableTable.WitnessBuild.scoped_trace entry first codes codeTable codeCount codeMaximum codeSlices stp pad scratch actual "codedb" codeArguments afterCodes codeArgs outcome continued with stopped|reached
    · have finalClock : post.clock=first.clock := by rw [endpoint]; rfl
      have firstCost:=nodeReturned.cost
      have firstForward:=nodeReturned.forward
      have secondForward:=evaluateHOLFiniteState_clock_le entry afterNodes
      have continuedOriginal : evaluateHOLFiniteState entry afterNodes=(outcome,first) := by rw [shapes.2.2.2.2.2.2.2]; exact continued
      rw [continuedOriginal] at secondForward
      change nodeTarget.clock-first.clock≤MutableTable.WitnessBuild.bodyPrice codeSlices codeCount+1 at stopped
      rw [finalClock]
      exact Or.inl (by omega)
    · obtain ⟨codeTarget,inner,codeReturned,remaining,restored⟩ := reached
      have nodeDatabase:=nodeReturned.toNormal.database_after_build source nodeTarget entry codeTarget nodes heap nodeCount nodeMaximum nodeSlices codes codeTable codeCount stp pad scratch nodeInputs
        rfl actual.heapGlobal codeReturned.toNormal stateArena padArena scratchArena
        (by constructor; omega; constructor <;> omega)
      have codeDatabase:=codeReturned.toNormal.database entry codeTarget codes codeTable codeCount codeMaximum codeSlices stp pad scratch actual
      obtain ⟨currentHeap,currentHeapCell,nodeBefore,codeBefore⟩ := nodeReturned.toNormal.before_after_build source nodeTarget entry codeTarget nodes heap nodeCount nodeMaximum nodeSlices codes codeTable codeCount stp pad scratch nodeInputs
        rfl codeReturned.toNormal stateArena padArena scratchArena (by constructor; omega; constructor <;> omega)
      exact Or.inr ⟨nodeTarget,codeTarget,codeTable,currentHeap,inner,nodeReturned,codeReturned,nodeDatabase,codeDatabase,currentHeapCell,nodeBefore,codeBefore,remaining,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.constructors_trace
