import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Returned
import InitECandidate.Solver.Input.CurrentTable.ImageIntervalFrame

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact

/-- A real later database builder preserves every earlier Patricia table
whose full allocation lies below its protected incoming heap frontier. -/
theorem Returned.prior_image {data : Data} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table cap priorTable priorCap root : BitVec 64} {next count : Nat}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (result : Returned data source post table cap)
    (image : Image source priorTable priorCap root next count valid bits left right keys ValueOf)
    (little : source.be=false) (lower : data.lower≤priorTable.toNat)
    (upper : (New.endPointer priorTable priorCap).toNat≤data.upper) :
    Image post priorTable priorCap root next count valid bits left right keys ValueOf := by
  have domain := result.arena.domain.trans image.domain.symm
  have endian := result.little.trans little.symm
  apply image.of_interval domain endian
  exact ⟨by intro query low high; exact result.input.words query (by omega) (by omega)⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.Returned.prior_image
