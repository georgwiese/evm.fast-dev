import InitECandidate.Solver.Input.MainRunAttemptConstructorReached
import InitECandidate.Solver.MutableTable.WitnessDatabaseFields

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- Actual immutable tables, their real caller locals and the current heap
at the original state_init caller. Root/header reads are separate obligations. -/
def StateInitBoundary (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ codeArray nodeTable codeTable heap,
    MutableTable.WitnessBuild.Database current (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) nodeTable (nodeCount input) 1024 (nodeSlices input) 2713717584#64 ∧
    MutableTable.WitnessBuild.Database current (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) 65536 (codeSlices input) 2713717584#64 ∧
    current.locals.lookup (ofString "nodedb")=some (.val (.word nodeTable)) ∧
    current.locals.lookup (ofString "codedb")=some (.val (.word codeTable)) ∧
    current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    MutableTable.WitnessBuild.BeforeHeap current nodeTable heap.toNat ∧ MutableTable.WitnessBuild.BeforeHeap current codeTable heap.toNat

/-- Extract this context at the genuine afterCodes execution already
reached by main's unchanged verification/header/constructor prefix. -/
theorem Reached.state_init_boundary (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (outcome : Option (PanSemResultExact 64)) (reached : Reached input source post root outcome) :
    ∃ current inner,StateInitBoundary input current ∧ evaluateHOLFiniteState current RunAttempt.afterCodes=(outcome,inner) := by
  obtain ⟨headerTarget,headerRows,parent,nodeTarget,codeTarget,codeArray,heap,codeTable,currentHeap,inner,headerReturned,nodeReturned,codeReturned,nodeDatabase,codeDatabase,heapCell,nodeBefore,codeBefore,forward,spent,continued,endpoint⟩ := reached
  let afterHeader:=parentSource source headerTarget input root
  let prepared:=RunAttempt.constructorEntry afterHeader (countWord input) (hashArray input root) parent
  let codeSource:=RunAttempt.codeEntry prepared nodeTarget heap
  let current:=CallNormal.continuationEntry codeSource codeTarget "codedb" (.val (.word codeTable))
  have nodeData:=nodeDatabase.of_fields codeTarget current _ heap _ _ _ _ rfl rfl rfl
  have codeData:=codeDatabase.of_fields codeTarget current _ codeTable _ _ _ _ rfl rfl rfl
  have nodeCell : current.locals.lookup (ofString "nodedb")=some (.val (.word heap)) :=
    (CallNormal.continuation_lookup_other codeSource codeTarget "codedb" "nodedb" (.val (.word codeTable)) (by decide)).trans
      (CallNormal.continuation_lookup_same prepared nodeTarget "nodedb" (.val (.word heap)))
  have codeCell : current.locals.lookup (ofString "codedb")=some (.val (.word codeTable)) := CallNormal.continuation_lookup_same _ _ _ _
  refine ⟨current,inner,⟨codeArray,heap,codeTable,currentHeap,nodeData,codeData,nodeCell,codeCell,heapCell,nodeBefore,codeBefore⟩,continued⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.Reached.state_init_boundary
