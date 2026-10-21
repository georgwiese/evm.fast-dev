import InitECandidate.Solver.Mpt.StateInitRootStore

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def storageArguments : List (ExpHOL 64):=[.const 32#64,.const 64#64]
def afterStorageTable : ProgHOL 64:=match afterRootStore with | .decCall _ _ _ _ tail=>tail | _=>.skip
def afterStorageTrie : ProgHOL 64:=match afterStorageTable with | .seq _ tail=>tail | _=>.skip

set_option maxRecDepth 100000 in
theorem storage_shapes : afterRootStore=.decCall (ofString "t") .one (ofString "htab_new") storageArguments afterStorageTable ∧
    afterStorageTable=.seq (store 32 "t") afterStorageTrie := by
  simp only [afterRootStore,afterRoot,rootCall,afterSecond,afterFirst,afterAllocation,body,Guest.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none,storageArguments,afterStorageTable,afterStorageTrie,store,WitnessRadix.QueryBranch.localVar]
  trivial

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.storage_shapes
