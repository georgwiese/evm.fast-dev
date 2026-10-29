import InitECandidate.Solver.Input.CurrentVerify.DatabaseReturned
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual database result advances the heap while retaining the
complete decoded SI/payload/gas and all three original witness arrays at
the real scoped caller continuation. -/
theorem after_database_data {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array table cap : BitVec 64} {start length boundary limit upper : Nat}
    (data : Data input source pointer si record gasWord boundary) (name : String) (different : ofString name≠ofString "si")
    (before : boundary≤upper)
    (returned : CurrentTable.NodeBuild.Returned {databaseData input array pointer start length boundary limit with upper:=upper} source target table cap) :
    Data input (CallNormal.continuationEntry source target name (.val (.word table))) pointer si record gasWord boundary := by
  let ready := CallNormal.continuationEntry source target name (.val (.word table))
  have arena : CurrentStartup.ArenaState ready := returned.arena.of_frame rfl
  have environment : CurrentKeccak.Hash.Environment ready 2701132160#64 2701132360#64 := returned.environment.of_frame rfl
  have siLocal : ready.locals.lookup (ofString "si")=some (.val (.word si)) :=
    (CallNormal.continuation_lookup_other source target name "si" (.val (.word table)) different).trans data.siLocal
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,countBound⟩ := returned.image
  have geometry : CurrentTable.New.Geometry table cap := image.geometry
  have endAfter : table.toNat+88≤(CurrentTable.New.endPointer table cap).toNat := by
    have a:=geometry.tableBefore
    have b:=geometry.keysBefore
    have c:=geometry.nodesBefore
    have d:=geometry.orderBefore
    omega
  obtain ⟨heap,heapCell,heapLower,heapUpper,heapAligned⟩ := returned.heap
  have heap : NormalHeapEffects.AtLeast (boundary+32) ready :=
    ⟨heap,heapCell,by have := returned.tableAfter; change upper≤table.toNat at this; omega,heapUpper,heapAligned⟩
  exact data.of_interval arena returned.little environment returned.outCell ((returned.globals _ (by decide)).trans data.mptKey) ((returned.globals _ (by decide)).trans data.mptEmpty)
    ((returned.globals _ (by decide)).trans data.shaState) ((returned.globals _ (by decide)).trans data.shaPad) ((returned.globals _ (by decide)).trans data.u256) heap siLocal
    (fun query low high=>returned.input.words query low (by change query.toNat<upper; omega))

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.after_database_data
