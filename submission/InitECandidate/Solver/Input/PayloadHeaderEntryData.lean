import InitECandidate.Solver.Input.MainRunAttemptPayloadHeaderEntry

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem PayloadHeaderEntry.little (input : Guest.InputBlob)
    (origin initializer entry : PanSemStateFiniteExact 64 Guest.HostMemory) (root workspace nodes stateRoot codes : BitVec 64)
    (ready : PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes) : entry.be=false := by
  obtain ⟨installed,scalars,scratch,globals,code,domain,endian,oracle,heap,trieRoot,storage,heapCell,arena,aligned,view,frozen,rest⟩:=ready.state
  obtain ⟨array,nodeTable,codeTable,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=frozen
  exact nodeData.little

/-- The first original payload_header declaration reads the true decoded
payload pointer from preserved SI storage, using its actual mapped layout. -/
theorem PayloadHeaderEntry.payload_read (input : Guest.InputBlob)
    (origin initializer entry : PanSemStateFiniteExact 64 Guest.HostMemory) (root workspace nodes stateRoot codes : BitVec 64)
    (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes) :
    eval entry (RequestRootHash.fieldExpression 0)=some (.val (.word (PayloadPrefix.cursor input))) := by
  let data:=RequestRootHashData.description input counts
  exact data.field_read origin entry _ _ _ prepared.image prepared.layout ready.inputFrame ready.environment.domain ready.si
    (0,data.payload.payload) (by simp [RequestRootHash.Description.cells])

/-- At the actual next local scope, PL_RAW is the original copied payload
buffer. This uses the same old-region agreement, with no future read premise. -/
theorem PayloadHeaderEntry.raw_read (input : Guest.InputBlob)
    (origin initializer entry : PanSemStateFiniteExact 64 Guest.HostMemory) (root workspace nodes stateRoot codes : BitVec 64)
    (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes) :
    eval (QueryBranch.bind entry "pl" (PayloadPrefix.cursor input)) (PayloadHash.fieldExpression 0)=
      some (.val (.word (inputPointer+62#64))) := by
  let data:=PayloadHashData.description input
  let next:=QueryBranch.bind entry "pl" (PayloadPrefix.cursor input)
  have frame:=ready.inputFrame.of_memory origin entry next _ _ rfl
  exact data.field_read origin next _ _ _ prepared.image.payload prepared.layout.payload frame ready.environment.domain
    (bind_lookup_same _ _ _) (0,data.raw) (by simp [PayloadHash.Description.cells])

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.PayloadHeaderEntry.little
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.PayloadHeaderEntry.payload_read
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.PayloadHeaderEntry.raw_read
