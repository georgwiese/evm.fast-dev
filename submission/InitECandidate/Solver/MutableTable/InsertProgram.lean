import InitECandidate.Solver.MutableTable.MaskedPath
import InitECandidate.Solver.MutableTable.FindHeader
import InitECandidate.Solver.WitnessRadix.Copy32Call

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def body : ProgHOL 64:=match Guest.guestFn_htab_insert_raw with | .function fn=>progToHOL fn.body | _=>.skip
def increment : ProgHOL 64:=.assign .local (ofString "i") Find.nextIndex
def loop : ProgHOL 64:=.while Find.condition increment
def scaled (base : ExpHOL 64) (index : String) (stride : ExpHOL 64) : ExpHOL 64:=
  .op .add [base,.panop .mul [localVar index,stride]]
def valueStore : ProgHOL 64:=.store (scaled (Find.tableLoad 40#64) "i" (.const 8#64)) (localVar "value")
def usedStore : ProgHOL 64:=.storeByte (.op .add [localVar "used",localVar "i"]) (.const 1#64)
def orderStore : ProgHOL 64:=.store (scaled (localVar "order") "n" (.const 8#64)) (localVar "i")
def positionStore : ProgHOL 64:=.store (scaled (localVar "order_pos") "i" (.const 8#64)) (localVar "n")
def countStore : ProgHOL 64:=.store (.op .add [localVar "t",.const 24#64]) (.op .add [localVar "n",.const 1#64])
def returnZero : ProgHOL 64:=.return (.const 0#64)
def afterCount : ProgHOL 64:=.seq orderStore (.seq positionStore (.seq countStore returnZero))
def afterUsed : ProgHOL 64:=.dec (ofString "n") .one (Find.tableLoad 24#64) afterCount
def afterCopy : ProgHOL 64:=.seq valueStore (.seq usedStore afterUsed)
def copyCall : ProgHOL 64:=.call (some (none,none)) (ofString "memcpy")
  [Find.keyAddress,localVar "key",localVar "klen"]
def afterLoop : ProgHOL 64:=.seq copyCall afterCopy
def afterIndex : ProgHOL 64:=.seq loop afterLoop
def afterHash : ProgHOL 64:=.dec (ofString "i") .one Find.initialIndex afterIndex
def headerActions : List Action:=Find.headerActions++
  [.declare "order" (Find.tableLoad 56#64),.declare "order_pos" (Find.tableLoad 64#64)]

theorem body_shape : body=program headerActions
    (.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key",localVar "klen"] afterHash) := by
  simp only [body,Guest.guestFn_htab_insert_raw,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    headerActions,Find.headerActions,List.cons_append,List.nil_append,program,afterHash,afterIndex,loop,increment,
    afterLoop,copyCall,afterCopy,valueStore,usedStore,afterUsed,afterCount,orderStore,positionStore,countStore,
    returnZero,scaled,Find.tableLoad,Find.initialIndex,Find.mask,Find.condition,Find.usedLoad,Find.nextIndex,
    Find.keyAddress,localVar,Option.map_none]

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.body_shape
