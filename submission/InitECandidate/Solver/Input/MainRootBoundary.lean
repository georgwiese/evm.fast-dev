import InitECandidate.Solver.Input.MainStateInitEntryData

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- Both original databases at a genuine root decoder state. Its node
table is identified by the root decoder's real db formal. -/
def RootBoundary (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ codeArray nodeTable codeTable heap,
    MutableTable.WitnessBuild.Database current (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) nodeTable (nodeCount input) 1024 (nodeSlices input) 2713717584#64 ∧
    MutableTable.WitnessBuild.Database current (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) 65536 (codeSlices input) 2713717584#64 ∧
    current.locals.lookup (ofString "db")=some (.val (.word nodeTable)) ∧
    current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧
    MutableTable.WitnessBuild.BeforeHeap current nodeTable heap.toNat ∧ MutableTable.WitnessBuild.BeforeHeap current codeTable heap.toNat

/-- Only the actual callee local name changes at root entry; all physical
data is transported through the exact nonlocal frame. -/
theorem RootBoundary.of_state_init (input : Guest.InputBlob) (source entry : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : StateInitBoundary input source) (frame : LocalEffects.erase entry=LocalEffects.erase source)
    (nodes : entry.locals.lookup (ofString "db")=source.locals.lookup (ofString "nodedb")) : RootBoundary input entry := by
  obtain ⟨codeArray,nodeTable,codeTable,heap,nodeDatabase,codeDatabase,nodeCell,codeCell,heapCell,arena,aligned,nodeBefore,codeBefore⟩ := actual
  have memory:=LocalEffects.memory_of_erase source entry frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change entry.globals=source.globals at globals
  have nodeData:=nodeDatabase.of_fields source entry _ nodeTable _ _ _ _ memory.symm domain.symm endian.symm
  have codeData:=codeDatabase.of_fields source entry _ codeTable _ _ _ _ memory.symm domain.symm endian.symm
  have kept (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap source table heap.toNat) : MutableTable.WitnessBuild.BeforeHeap entry table heap.toNat := by
    obtain ⟨capacity,cell,bound⟩ := before
    exact ⟨capacity,(congrFun memory _).trans cell,bound⟩
  exact ⟨codeArray,nodeTable,codeTable,heap,nodeData,codeData,nodes.trans nodeCell,
    by rw [globals]; exact heapCell,arena,aligned,kept nodeTable nodeBefore,kept codeTable codeBefore⟩

theorem RootBoundary.erase_frame (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : RootBoundary input source) (frame : LocalEffects.erase current=LocalEffects.erase source)
    (nodes : current.locals.lookup (ofString "db")=source.locals.lookup (ofString "db")) : RootBoundary input current := by
  obtain ⟨codeArray,nodeTable,codeTable,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,arena,aligned,nodeBefore,codeBefore⟩ := actual
  have memory:=LocalEffects.memory_of_erase source current frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change current.globals=source.globals at globals
  have nodeData:=nodeDatabase.of_fields source current _ nodeTable _ _ _ _ memory.symm domain.symm endian.symm
  have codeData:=codeDatabase.of_fields source current _ codeTable _ _ _ _ memory.symm domain.symm endian.symm
  have kept (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap source table heap.toNat) : MutableTable.WitnessBuild.BeforeHeap current table heap.toNat := by
    obtain ⟨capacity,cell,bound⟩ := before
    exact ⟨capacity,(congrFun memory _).trans cell,bound⟩
  exact ⟨codeArray,nodeTable,codeTable,heap,nodeData,codeData,nodes.trans nodeCell,
    by rw [globals]; exact heapCell,arena,aligned,kept nodeTable nodeBefore,kept codeTable codeBefore⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.of_state_init
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.erase_frame
