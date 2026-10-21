import InitECandidate.Solver.Input.MainRootBoundary

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real node database ends before the actual current heap, whose
arena supplies the original finite persistent-memory ceiling. -/
theorem RootBoundary.db_upper (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db))) : db.toNat≤33806089496 := by
  obtain ⟨codeArray,nodes,codes,heap,nodeData,codeData,nodeCell,heapCell,arena,aligned,nodeBefore,codeBefore⟩:=boundary
  have same : nodes=db := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nodeCell.symm.trans dbCell)))
  obtain ⟨capacity,stored,before⟩:=nodeBefore
  have upper:=arena.upper
  rw [same] at before
  omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.db_upper
