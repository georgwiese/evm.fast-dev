import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Returned

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact

/-- The same physical builder result crosses its actual callee/caller
local and clock restoration, retaining the original input region. -/
theorem Returned.of_frames {data : Data} {origin source post target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table cap : BitVec 64} (result : Returned data source post table cap)
    (entry : LocalEffects.erase source=LocalEffects.erase origin)
    (exit : LocalEffects.erase target=LocalEffects.erase post) : Returned data origin target table cap := by
  have inMemory := LocalEffects.memory_of_erase origin source entry
  have outMemory := LocalEffects.memory_of_erase post target exit
  have inGlobals := congrArg PanSemStateFiniteExact.globals entry
  have outGlobals := congrArg PanSemStateFiniteExact.globals exit
  have endian := congrArg PanSemStateFiniteExact.be exit
  change source.globals=origin.globals at inGlobals
  change target.globals=post.globals at outGlobals
  change target.be=post.be at endian
  obtain ⟨heap,cell,lower,upper,aligned⟩ := result.heap
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bound⟩ := result.image
  exact ⟨result.arena.of_frame exit,endian.trans result.little,result.environment.of_frame exit,
    (by rw [outGlobals]; exact result.outCell),⟨heap,by rw [outGlobals]; exact cell,lower,upper,aligned⟩,
    ⟨by intro query lower upper; exact (congrFun outMemory query).trans ((result.input.words query lower upper).trans (congrFun inMemory query))⟩,
    (fun key different=>(congrArg (fun globals=>globals.lookup key) outGlobals).trans
      ((result.globals key different).trans (congrArg (fun globals=>globals.lookup key) inGlobals))),
    ⟨root,next,count,valid,bits,left,right,keys,image.of_frame exit,bound⟩,result.tableAfter,result.totalBound⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.Returned.of_frames
