import InitECandidate.Solver.Input.MainStateInitRuntime

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual caller/callee local replacement leaves all physical database,
heap and allocation-frontier facts intact. Two real ABI bindings identify
the same table words at the new entry. -/
theorem StateInitBoundary.at_entry (input : Guest.InputBlob) (source entry : PanSemStateFiniteExact 64 Guest.HostMemory)
    (actual : StateInitBoundary input source) (frame : LocalEffects.erase entry=LocalEffects.erase source)
    (nodes : entry.locals.lookup (ofString "nodedb")=source.locals.lookup (ofString "nodedb"))
    (codes : entry.locals.lookup (ofString "codedb")=source.locals.lookup (ofString "codedb")) : StateInitBoundary input entry := by
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
  exact ⟨codeArray,nodeTable,codeTable,heap,nodeData,codeData,nodes.trans nodeCell,codes.trans codeCell,
    by rw [globals]; exact heapCell,arena,aligned,kept nodeTable nodeBefore,kept codeTable codeBefore⟩

/-- Runtime metadata and every global remain available at a genuine pure
caller-to-callee entry. The erase equality retains the full FFI state too. -/
theorem runtime_of_entry (source entry : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : LocalEffects.erase entry=LocalEffects.erase source) : ConstructorRuntimeFrame source entry := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change entry.globals=source.globals at globals
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  have exceptions:=congrArg PanSemStateFiniteExact.eshapes frame
  have oracle:=congrArg (fun state=>state.ffi.oracle) frame
  exact ⟨LocalEffects.code_of_erase source entry frame,domain,endian,exceptions,oracle,
    by intro key h b n; rw [globals]⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.StateInitBoundary.at_entry
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.runtime_of_entry
