import InitECandidate.Solver.Input.MainStateInitBoundary
import InitECandidate.Solver.Input.ConstructorRuntimeEnvironment
import InitECandidate.Solver.Input.ConstructorRuntimeScalars
import InitECandidate.Solver.Input.ScopeClock

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- At the exact state_init caller reached by the original prefix, runtime
metadata and nonheap globals follow from the genuine header return and both
real constructor returns, rather than fresh entry assumptions. -/
theorem Reached.state_init_runtime (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (originalScalars : OriginalScalarGlobals.Scalars source.globals)
    (outcome : Option (PanSemResultExact 64)) (reached : Reached input source post root outcome) :
    ∃ current inner,StateInitBoundary input current ∧ ConstructorRuntimeFrame source current ∧
      OriginalCode.Installed current.code ∧ OriginalScalarGlobals.Scalars current.globals ∧ Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧
      Keccak256.Environment current 2713714976#64 2713715176#64 ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤price input ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current RunAttempt.afterCodes=(outcome,inner) := by
  obtain ⟨headerTarget,headerRows,parent,nodeTarget,codeTarget,codeArray,heap,codeTable,currentHeap,inner,headerReturned,nodeReturned,codeReturned,nodeDatabase,codeDatabase,heapCell,nodeBefore,codeBefore,forward,spent,continued,endpoint⟩ := reached
  let afterHeader:=parentSource source headerTarget input root
  let prepared:=RunAttempt.constructorEntry afterHeader (countWord input) (hashArray input root) parent
  let codeSource:=RunAttempt.codeEntry prepared nodeTarget heap
  let current:=CallNormal.continuationEntry codeSource codeTarget "codedb" (.val (.word codeTable))
  have front : ConstructorRuntimeFrame source headerTarget :=
    ⟨headerReturned.code,headerReturned.domain,headerReturned.endian,headerReturned.exceptions,headerReturned.oracle,
      fun key h b n=>headerReturned.globals key h⟩
  have afterFrame : ConstructorRuntimeFrame headerTarget afterHeader := CallNormal.continuation_runtime _ _ _ _
  have preparedFrame:=afterFrame.trans headerTarget afterHeader prepared (RunAttempt.constructor_runtime afterHeader _ _ parent)
  have nodeFrame:=ConstructorRuntimeFrame.of_constructor prepared nodeTarget _ heap _ _ _ _ nodeReturned.toNormal
  have callerFrame : ConstructorRuntimeFrame nodeTarget codeSource := CallNormal.continuation_runtime _ _ _ _
  have codeFrame:=ConstructorRuntimeFrame.of_constructor codeSource codeTarget _ codeTable _ _ _ _ codeReturned.toNormal
  have resumedFrame : ConstructorRuntimeFrame codeTarget current := CallNormal.continuation_runtime _ _ _ _
  have tailFrame:=preparedFrame.trans headerTarget prepared nodeTarget nodeFrame
  have tailFrame:=tailFrame.trans headerTarget nodeTarget codeSource callerFrame
  have tailFrame:=tailFrame.trans headerTarget codeSource codeTarget codeFrame
  have tailFrame:=tailFrame.trans headerTarget codeTarget current resumedFrame
  have frame:=front.trans source headerTarget current tailFrame
  have currentInstalled : OriginalCode.Installed current.code := by rw [frame.code]; exact installed
  have kept (key : MlS) (different : key≠ofString "heap_ptr") : current.globals.lookup key=prepared.globals.lookup key := by
    have first:=(nodeReturned.toNormal.fields prepared nodeTarget _ heap _ _ _ _).2.2.2.2.2
    have second:=(codeReturned.toNormal.fields codeSource codeTarget _ codeTable _ _ _ _).2.2.2.2.2
    exact (second key different).trans (first key different)
  have hashCells:=RunAttempt.constructor_hash_cells afterHeader (countWord input) (hashArray input root) parent
  have hashesCell : current.globals.lookup (ofString "block_hashes")=some (.val (.word (hashArray input root))) :=
    (kept _ (by decide)).trans hashCells.1
  have countCell : current.globals.lookup (ofString "block_hashes_n")=some (.val (.word (countWord input))) :=
    (kept _ (by decide)).trans hashCells.2
  have currentScalars:=frame.scalars source current originalScalars currentHeap (hashArray input root) (countWord input) heapCell hashesCell countCell
  have scratch:=tailFrame.scratch headerTarget current 2713714688#64 2701135872#64 headerReturned.arena
  have environment:=tailFrame.hash_environment headerTarget current 2713714976#64 2713715176#64 headerReturned.environment
  have nodeData:=nodeDatabase.of_fields codeTarget current _ heap _ _ _ _ rfl rfl rfl
  have codeData:=codeDatabase.of_fields codeTarget current _ codeTable _ _ _ _ rfl rfl rfl
  have nodeCell : current.locals.lookup (ofString "nodedb")=some (.val (.word heap)) :=
    (CallNormal.continuation_lookup_other codeSource codeTarget "codedb" "nodedb" (.val (.word codeTable)) (by decide)).trans
      (CallNormal.continuation_lookup_same prepared nodeTarget "nodedb" (.val (.word heap)))
  have codeCell : current.locals.lookup (ofString "codedb")=some (.val (.word codeTable)) := CallNormal.continuation_lookup_same _ _ _ _
  have geometry:=codeReturned.toNormal.heap_arena codeSource codeTarget _ codeTable _ 2713714976#64 2713715176#64 2713717584#64 currentHeap heapCell
  have finalClock : post.clock=inner.clock := by
    have projected:=congrArg PanSemStateFiniteExact.clock endpoint
    simpa only [RunAttempt.restoreHeader_clock,RunAttempt.restoreConstructor_clock,QueryBranch.restore_clock] using projected
  exact ⟨current,inner,⟨codeArray,heap,codeTable,currentHeap,nodeData,codeData,nodeCell,codeCell,heapCell,geometry.1,geometry.2,nodeBefore,codeBefore⟩,
    frame,currentInstalled,currentScalars,scratch,environment,forward,spent,finalClock,continued⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.Reached.state_init_runtime
