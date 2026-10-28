import InitECandidate.Solver.Input.CurrentTable.NodeBuildConstructor

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def row : ExpHOL 64 := .op .add [localVar "slice_arr",.panop .mul [localVar "i",.const 16#64]]
def hashArguments : List (ExpHOL 64) := [.load .one row,.load .one (.op .add [localVar "slice_arr",.panop .mul [localVar "i",.const 16#64],.const 8#64]),.var .global (ofString "mpt_hash_scratch")]
def hashCall : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256") hashArguments
def setArguments : List (ExpHOL 64) := [localVar "t",.var .global (ofString "mpt_hash_scratch"),row]
def setCall : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set") setArguments
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def iteration : ProgHOL 64 := .seq hashCall (.seq setCall increment)
def condition : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")
def loop : ProgHOL 64 := .while condition iteration
def returnTable : ProgHOL 64 := .return (localVar "t")

set_option maxRecDepth 100000 in
theorem table_tail_shape : tableTail = .dec (ofString "i") .one (.const 0#64) (.seq loop returnTable) := by
  simp only [tableTail,allocatedTail,afterCap,body,Guest.Software.guestFn_nodedb_build,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,loop,condition,iteration,hashCall,hashArguments,setCall,setArguments,increment,returnTable,row,localVar]

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.table_tail_shape
