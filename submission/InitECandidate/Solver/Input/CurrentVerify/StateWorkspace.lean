import InitECandidate.Solver.Input.CurrentVerify.DatabaseContext
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LookupFrame
import InitECandidate.Solver.Mpt.StateInitPrefixFrame

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Main's matching decoded witness and physical node database survive the
actual state workspace allocation/stores, even though ws and heap globals
change. The relevant memory ends before that real incoming heap. -/
theorem state_workspace_node_image {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap heap root codes : BitVec 64} {start length boundary : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31))
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (arena : CurrentStartup.ArenaState source) (room : heap.toNat+40≤2952790016)
    (inputBefore : boundary≤heap.toNat) (tableBefore : (CurrentTable.New.endPointer table cap).toNat≤heap.toNat) :
    let current:=Mpt.StateInit.ready source heap table root codes
    CurrentStartup.ArenaState current ∧
    CurrentStartup.WitnessArrays.Image input current pointer si array start length boundary 40 1024 (2^31) ∧
    CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} current (VarList.decodedCount input start length) := by
  let current:=Mpt.StateInit.ready source heap table root codes
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : current.memory query=source.memory query :=
    Mpt.StateInit.ready_memory_before source heap table root codes query room before
  refine ⟨Mpt.StateInit.ready_arena source heap table root codes arena,?_,?_⟩
  · exact witness.of_interval (by decide) (by intro query low high; exact memory query (by omega))
  · exact tableImage.of_interval rfl rfl (by intro query low high; exact memory query (by change query.toNat<(CurrentTable.New.endPointer table cap).toNat at high; omega))

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.state_workspace_node_image
