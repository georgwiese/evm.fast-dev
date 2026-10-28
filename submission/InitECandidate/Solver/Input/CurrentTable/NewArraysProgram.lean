import InitECandidate.Solver.Input.CurrentTable.NewKeysEntry
import InitECandidate.Solver.Input.CurrentTable.ArrayAllocation

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterKeys : ProgHOL 64 := match keysCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def nodesCall : ProgHOL 64 := match afterKeys with | .seq _ rest=>rest | _=>.skip
def afterNodes : ProgHOL 64 := match nodesCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def orderCall : ProgHOL 64 := match afterNodes with | .seq _ rest=>rest | _=>.skip
def afterOrder : ProgHOL 64 := match orderCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def finalFields : ProgHOL 64 := match afterOrder with | .seq _ rest=>rest | _=>.skip

def keyAmount : ExpHOL 64 := .panop .mul [.op .add [localVar "ncap",.const 1#64],localVar "stride"]
def nodeAmount : ExpHOL 64 := .panop .mul [.op .add [localVar "ncap",.const 1#64],.const 32#64]
def orderAmount : ExpHOL 64 := .panop .mul [.op .add [localVar "ncap",.const 1#64],.const 8#64]
def size32 (cap : BitVec 64) : BitVec 64 := (cap+1#64)*32#64
def size8 (cap : BitVec 64) : BitVec 64 := (cap+1#64)*8#64

set_option maxRecDepth 100000 in
theorem array_shapes :
    keysCall=.decCall (ofString "keys") .one (ofString "alloc") [keyAmount]
      (.seq (.store (Scalar.plus (localVar "t") 32) (localVar "keys")) nodesCall) ∧
    nodesCall=.decCall (ofString "nodes") .one (ofString "alloc") [nodeAmount]
      (.seq (.store (Scalar.plus (localVar "t") 40) (localVar "nodes")) orderCall) ∧
    orderCall=.decCall (ofString "order") .one (ofString "alloc") [orderAmount]
      (.seq (.store (Scalar.plus (localVar "t") 48) (localVar "order")) finalFields) := by
  simp only [keysCall,afterKeys,nodesCall,afterNodes,orderCall,afterOrder,finalFields,keyAmount,nodeAmount,orderAmount,
    fields,afterNcap,afterStride,afterTable,body,Guest.Software.guestFn_htab_new,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Scalar.plus,localVar,CallPrefix.cutAt]
  trivial

theorem keys_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cap : BitVec 64)
    (ncapCell : source.locals.lookup (ofString "ncap")=some (.val (.word cap)))
    (strideCell : source.locals.lookup (ofString "stride")=some (.val (.word 32#64))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [keyAmount]=some (WitnessRadix.PersistentAlloc.values (size32 cap)) := by
  simp [keyAmount,size32,WitnessRadix.PersistentAlloc.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,
    ncapCell,strideCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.array_shapes
#print axioms InitECandidate.Solver.Input.CurrentTable.New.keys_arguments
