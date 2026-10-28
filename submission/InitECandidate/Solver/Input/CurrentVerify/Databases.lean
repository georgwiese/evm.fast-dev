import InitECandidate.Solver.Input.CurrentVerify.DatabaseCall
import InitECandidate.Solver.Input.CurrentVerify.CodeEntry
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.PriorReturned

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The same two actual current database calls either stop within their
combined allowance or reach the original state_init continuation. Both
physical tables survive, including the first table through the second build. -/
theorem databases_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source nodeCall=(outcome,post)) :
    source.clock-post.clock≤3323240764 ∨
    ∃ first current inner nodeArray nodeStart nodeLength codeArray codeStart codeLength nodeTable nodeCap codeTable codeCap nodeUpper codeUpper,
      Data input current pointer si record gasWord boundary ∧
      CurrentTable.NodeBuild.Returned {databaseData input nodeArray pointer nodeStart nodeLength boundary 1024 with upper:=nodeUpper} source current nodeTable nodeCap ∧
      CurrentTable.NodeBuild.Returned {databaseData input codeArray pointer codeStart codeLength boundary 65536 with upper:=codeUpper} first current codeTable codeCap ∧
      current.locals.lookup (ofString "nodedb")=some (.val (.word nodeTable)) ∧
      current.locals.lookup (ofString "codedb")=some (.val (.word codeTable)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤3323240764 ∧
      evaluateHOLFiniteState current afterCodes=(outcome,inner) ∧
      post=restore source "nodedb" (restore first "codedb" inner) := by
  obtain ⟨nodeArray,nodeStart,nodeLength,nodeImage,nodeSmall,nodeArgs⟩ := node_arguments data
  rw [node_shape] at run
  rcases database_call_trace data nodeImage (by decide) nodeSmall "nodedb" (by decide) nodeArguments afterNodes nodeArgs outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨first,nodeInner,nodeTable,nodeCap,nodeUpper,firstData,nodeBefore,nodeHeap,nodeResult,nodeCell,nodeLocals,nodeForward,nodePrice,codeRun,endpoint⟩ := reached
    obtain ⟨codeArray,codeStart,codeLength,codeImage,codeSmall,codeArgs⟩ := code_arguments firstData
    rw [code_shape] at codeRun
    rcases database_call_trace firstData codeImage (by decide) codeSmall "codedb" (by decide) codeArguments afterCodes codeArgs outcome codeRun with stopped|reached
    · have postClock : post.clock=nodeInner.clock := by rw [endpoint]; rfl
      exact Or.inl (by rw [postClock]; omega)
    · obtain ⟨current,inner,codeTable,codeCap,codeUpper,currentData,codeBefore,codeHeap,codeResult,codeCell,codeLocals,codeForward,codePrice,continued,restored⟩ := reached
      have nodeEnd : (CurrentTable.New.endPointer nodeTable nodeCap).toNat≤codeUpper := by
        obtain ⟨heap,cell,lower,upper,aligned⟩ := nodeResult.heap
        have equal : heap=BitVec.ofNat 64 codeUpper := by
          simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using cell.symm.trans codeHeap
        rw [equal,BitVec.toNat_ofNat] at lower
        exact lower.trans (Nat.mod_le _ _)
      have nodeLower : 2701134824≤nodeTable.toNat := by
        have before := nodeResult.tableAfter
        change nodeUpper≤nodeTable.toNat at before
        have bound := data.recordInside
        omega
      have nextNode := nodeResult.after_builder codeResult (by change 2701134824≤2701134824; omega) nodeLower nodeEnd
      have currentNode : current.locals.lookup (ofString "nodedb")=some (.val (.word nodeTable)) :=
        (codeLocals (ofString "nodedb") (by decide)).trans nodeCell
      exact Or.inr ⟨first,current,inner,nodeArray,nodeStart,nodeLength,codeArray,codeStart,codeLength,nodeTable,nodeCap,codeTable,codeCap,nodeUpper,codeUpper,
        currentData,nextNode,codeResult,currentNode,codeCell,by omega,by omega,continued,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.databases_trace
