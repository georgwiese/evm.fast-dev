import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Entry

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact

/-- Protect every previously allocated object by choosing the actual
current heap as this builder's input-frame frontier. -/
theorem Entry.raise_upper {data : Data} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Entry data source) (upper : Nat) (after : data.upper≤upper)
    (heap : NormalHeapEffects.AtLeast upper source) : Entry {data with upper:=upper} source := by
  have rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower upper :=
    ⟨entry.rows.cells,entry.rows.rowArena,entry.rows.rowAligned,entry.rows.rowAfter,
      (by intro index inside; have := entry.rows.rowBefore index inside; omega),
      entry.rows.inputArena,entry.rows.inputAfter,
      (by intro index inside; have := entry.rows.inputBefore index inside; omega),entry.rows.sizeBound⟩
  exact ⟨⟨entry.workspace.arena,entry.workspace.environment,heap,by change 2701131776≤upper; have := entry.workspace.lowerDomain; omega⟩,
    entry.little,rows,entry.outCell,entry.arrayCell,entry.countCell,entry.totalSmall,entry.stateBefore,entry.padBefore,
    entry.outBefore,entry.outArena,entry.outAligned,(by change data.lower≤upper; have := entry.lowerUpper; omega),entry.lowerSmall,entry.lengths,entry.itemSmall⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.Entry.raise_upper
