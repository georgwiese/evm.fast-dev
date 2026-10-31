import InitECandidate.Solver.Input.CurrentVerify.Databases
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Returned

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Both genuine decoded-input databases and their actual caller bindings
at the original state_init cut. Their source states remain explicit. -/
def HasTables (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) : Prop :=
  Data input current pointer si record gasWord boundary ∧
  current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
  ∃ nodeSource codeSource nodeArray nodeStart nodeLength codeArray codeStart codeLength nodeTable nodeCap codeTable codeCap nodeUpper codeUpper,
    boundary≤nodeUpper ∧ boundary≤codeUpper ∧
    CurrentStartup.WitnessArrays.Image input current pointer si nodeArray nodeStart nodeLength boundary 40 1024 (2^31) ∧
    CurrentStartup.WitnessArrays.Image input current pointer si codeArray codeStart codeLength boundary 56 65536 (2^31) ∧
    CurrentTable.NodeBuild.Returned {databaseData input nodeArray pointer nodeStart nodeLength boundary 1024 with upper:=nodeUpper} nodeSource current nodeTable nodeCap ∧
    CurrentTable.NodeBuild.Returned {databaseData input codeArray pointer codeStart codeLength boundary 65536 with upper:=codeUpper} codeSource current codeTable codeCap ∧
    current.locals.lookup (ofString "nodedb")=some (.val (.word nodeTable)) ∧
    current.locals.lookup (ofString "codedb")=some (.val (.word codeTable))

/-- The actual complete header/gas/two-database prefix either stops within
its uniform source allowance or reaches state_init with all real inputs and
both table images intact. The later result remains its original continuation. -/
theorem to_state_init {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤3389449218 ∨ ∃ current inner,
      HasTables input current pointer si record gasWord boundary ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤3389449218 ∧
      evaluateHOLFiniteState current afterCodes=(outcome,inner) ∧ post.clock=inner.clock ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  rcases to_nodes data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨nodeSource,nodePost,nodeData,nodePayload,nodeForward,nodePrice,nodeRun,postClock,postFrame⟩ := reached
    rcases databases_trace nodeData outcome nodeRun with stopped|reached
    · exact Or.inl (by rw [postClock]; omega)
    · obtain ⟨first,current,inner,nodeArray,nodeStart,nodeLength,codeArray,codeStart,codeLength,nodeTable,nodeCap,codeTable,codeCap,nodeUpper,codeUpper,
        currentData,nodeBefore,codeBefore,nodeImage,codeImage,nodeResult,codeResult,nodeCell,codeCell,payloadLocals,forward,price,continued,endpoint⟩ := reached
      have tables : HasTables input current pointer si record gasWord boundary :=
        ⟨currentData,payloadLocals.trans nodePayload,nodeSource,first,nodeArray,nodeStart,nodeLength,codeArray,codeStart,codeLength,nodeTable,nodeCap,codeTable,codeCap,nodeUpper,codeUpper,
          nodeBefore,codeBefore,nodeImage,codeImage,nodeResult,codeResult,nodeCell,codeCell⟩
      have clock : nodePost.clock=inner.clock := by rw [endpoint]; rfl
      have frame : LocalEffects.erase nodePost=LocalEffects.erase inner := by rw [endpoint]; rfl
      exact Or.inr ⟨current,inner,tables,by omega,by omega,continued,postClock.trans clock,postFrame.trans frame⟩

/-- Main's genuine completed node builder and retained witness rows supply
exactly the physical database used by the current resolver, including its
real location before the current heap. The code builder has already run. -/
theorem HasTables.node_database {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (tables : HasTables input source pointer si record gasWord boundary) :
    ∃ nodeData : CurrentTable.NodeBuild.Data,
      CurrentTable.NodeLookup.Database source nodeData ∧
      source.locals.lookup (ofString "nodedb")=some (.val (.word nodeData.table)) ∧
      NormalHeapEffects.AtLeast (CurrentTable.New.endPointer nodeData.table nodeData.cap).toNat source := by
  obtain ⟨data,payloadLocal,nodeSource,codeSource,array,start,length,codeArray,codeStart,codeLength,table,cap,codes,codeCap,nodeUpper,codeUpper,
    nodeBefore,codeBefore,witness,codeWitness,nodeResult,codeResult,nodeCell,codeCell⟩:=tables
  let nodeData : CurrentTable.NodeBuild.Data:={databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap}
  have image : CurrentTable.NodeBuild.ImageUpTo nodeData source nodeData.total:=nodeResult.image
  have rows:=witness.rows data.arena.domain (by decide)
  have beforeTable : boundary≤table.toNat:=nodeBefore.trans nodeResult.tableAfter
  exact ⟨nodeData,⟨image,rows,witness.lengths,by change 2701131776≤2701134824; decide,beforeTable⟩,nodeCell,nodeResult.heap⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_state_init

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.HasTables.node_database
