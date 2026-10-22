import InitECandidate.Solver.Mpt.StateInitBlockModels

namespace InitECandidate.Solver.Mpt.StateInit.Block
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

/-- Lexical return/restore changes no owned block, table or journal data. -/
theorem Initialized.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap workspace : BitVec 64)
    (initialized : Initialized source heap workspace) (globals : target.globals=source.globals)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) :
    Initialized target heap workspace:=by
  obtain ⟨bs,ws,ancestorHead,ancestorCount,family,pointers,zone,image,cap,journal,counter,transaction⟩:=initialized
  refine ⟨?_,?_,?_,?_,?_,?_,zone,?_,?_,?_,?_,?_⟩
  · rewrite [globals]; exact bs
  · rewrite [memory]; exact ws
  · rewrite [memory]; exact ancestorHead
  · rewrite [memory]; exact ancestorCount
  · exact family.of_pools (by rewrite [globals]; rfl) domain endian (fun _ _ _ _=>congrFun memory _)
  · intro index; rewrite [memory]; exact pointers index
  · intro entries; exact GasBudget.Journal.Image.empty target _ _ entries
  · rewrite [globals]; exact cap
  · rewrite [globals]; exact journal
  · rewrite [globals]; exact counter
  · rewrite [globals]; exact transaction

end InitECandidate.Solver.Mpt.StateInit.Block

#print axioms InitECandidate.Solver.Mpt.StateInit.Block.Initialized.of_fields
