import InitECandidate.Solver.MutableTable.LayoutEarlier32
import InitECandidate.Solver.WitnessRadix.ConstructorProgram

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def body : ProgHOL 64:=match Guest.guestFn_nodedb_build with | .function fn=>progToHOL fn.body | _=>.skip
def setArguments : List (ExpHOL 64):=[localVar "t",Constructor.scratch,Constructor.scaled "slice_arr" 16#64]
def increment : ProgHOL 64:=.assign .local (ofString "i") (addConst (localVar "i") 1#64)
def afterHash : ProgHOL 64:=.seq (.call (some (none,none)) (ofString "htab_set") setArguments) increment
def recordBody : ProgHOL 64:=.seq (.call (some (none,none)) (ofString "keccak256") Constructor.hashArguments) afterHash
def recordLoop : ProgHOL 64:=.while Constructor.condition recordBody
def tableTail : ProgHOL 64:=.dec (ofString "i") .one (.const 0#64) (.seq recordLoop (.return (localVar "t")))

theorem body_shape : body=.dec (ofString "cap") .one (.const 4#64)
    (.seq Constructor.capacityLoop (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,localVar "cap"] tableTail)) := by
  simp only [body,Guest.guestFn_nodedb_build,Constructor.capacityLoop,Constructor.body,RawProgram.guestFn_nodedb_build,
    BuildProgram.loops,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.append_nil,List.getElem?_cons_zero,Option.getD_some,tableTail,recordLoop,recordBody,afterHash,setArguments,increment,
    Constructor.condition,Constructor.hashArguments,Constructor.scratch,Constructor.scaled,localVar,addConst,Option.map_none]

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) (index : Nat) : Prop where
  table : source.locals.lookup (ofString "t")=some (.val (.word (BitVec.ofNat 64 plan.table)))
  records : source.locals.lookup (ofString "slice_arr")=some (.val (.word (BitVec.ofNat 64 plan.records)))
  count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 plan.count)))
  index : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))

def recordAddress (plan : AllocatedLayout.Plan) (index : Nat) : BitVec 64:=
  BitVec.ofNat 64 plan.records+BitVec.ofNat 64 index*16#64

theorem set_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) (index : Nat)
    (locals : Locals source plan index) (scratch : BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) setArguments=
      some (TableCall.values (BitVec.ofNat 64 plan.table) scratch (recordAddress plan index)) := by
  simp [setArguments,Constructor.scratch,Constructor.scaled,recordAddress,TableCall.values,localVar,
    evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,locals.table,locals.records,locals.index,global,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.body_shape
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.set_arguments
