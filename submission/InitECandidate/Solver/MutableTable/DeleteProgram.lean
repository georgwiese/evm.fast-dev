import InitECandidate.Solver.MutableTable.FindProgram
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix.ProgramPrefix

def body : ProgHOL 64 := match Guest.guestFn_htab_del with | .function fn => progToHOL fn.body | _ => .skip
def scaled (pool index : String) (step : ExpHOL 64) : ExpHOL 64 := .op .add [localVar pool, .panop .mul [localVar index, step]]
def keyAddress (index : String) : ExpHOL 64 := scaled "keys" index (localVar "stride")
def wordAddress (pool index : String) : ExpHOL 64 := scaled pool index (.const 8#64)
def positionRead (index : String) : ExpHOL 64 := .load .one (wordAddress "order_pos" index)
def nextJ : ExpHOL 64 := .op .and [.op .add [localVar "j", .const 1#64], Find.mask]
def incrementJ : ProgHOL 64 := .assign .local (ofString "j") nextJ
def usedLoad : ExpHOL 64 := .loadByte (.op .add [localVar "used", localVar "j"])
def emptyTest : ExpHOL 64 := .cmp .equal usedLoad (.const 0#64)
def truth (expression : ExpHOL 64) : ExpHOL 64 := .cmp .notEqual (.const 0#64) expression
def beforeHome : ExpHOL 64 := .cmp .notLower (localVar "i") (localVar "home")
def afterHome : ExpHOL 64 := .cmp .lower (localVar "j") (localVar "home")
def setMovable : ProgHOL 64 := .assign .local (ofString "movable") (.const 1#64)
def decision : ProgHOL 64 := .ite (.cmp .notLower (localVar "j") (localVar "i"))
  (.ite (truth (.op .or [beforeHome, afterHome])) setMovable .skip)
  (.ite (.op .and [truth beforeHome, truth afterHome]) setMovable .skip)
def copyCall : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy") [keyAddress "i", keyAddress "j", localVar "klen"]
def valueStore : ProgHOL 64 := .store (wordAddress "vals" "i") (.load .one (wordAddress "vals" "j"))
def orderStore : ProgHOL 64 := .store (wordAddress "order" "moved_pos") (localVar "i")
def positionStore : ProgHOL 64 := .store (wordAddress "order_pos" "i") (localVar "moved_pos")
def moveIndex : ProgHOL 64 := .assign .local (ofString "i") (localVar "j")
def moveBranch : ProgHOL 64 := .seq copyCall (.seq valueStore
  (.dec (ofString "moved_pos") .one (positionRead "j") (.seq orderStore (.seq positionStore moveIndex))))
def afterHash : ProgHOL 64 := .dec (ofString "home") .one (.op .and [localVar "h", Find.mask])
  (.dec (ofString "movable") .one (.const 0#64) (.seq decision
    (.ite (.cmp .notEqual (localVar "movable") (.const 0#64)) moveBranch .skip)))
def hashCall : ProgHOL 64 := .decCall (ofString "h") .one (ofString "htab_hash") [keyAddress "j", localVar "klen"] afterHash
def loopBody : ProgHOL 64 := .seq incrementJ (.seq (.ite emptyTest .break .skip) hashCall)
def loop : ProgHOL 64 := .while (.const 1#64) loopBody
def clearUsed : ProgHOL 64 := .storeByte (.op .add [localVar "used", localVar "i"]) (.const 0#64)
def lastTest : ExpHOL 64 := .cmp .notEqual (localVar "deleted_pos") (localVar "last_pos")
def lastBranch : ProgHOL 64 := .dec (ofString "last_slot") .one (.load .one (wordAddress "order" "last_pos"))
  (.seq (.store (wordAddress "order" "deleted_pos") (localVar "last_slot"))
    (.store (wordAddress "order_pos" "last_slot") (localVar "deleted_pos")))
def countStore : ProgHOL 64 := .store (.op .add [localVar "t", .const 24#64]) (localVar "last_pos")
def returnZero : ProgHOL 64 := .return (.const 0#64)
def returnOne : ProgHOL 64 := .return (.const 1#64)
def afterLoop : ProgHOL 64 := .seq clearUsed (.dec (ofString "n") .one (Find.tableLoad 24#64)
  (.dec (ofString "last_pos") .one (.op .sub [localVar "n", .const 1#64])
    (.seq (.ite lastTest lastBranch .skip) (.seq countStore returnOne))))
def afterHeaders : ProgHOL 64 := .dec (ofString "deleted_pos") .one (positionRead "i")
  (.dec (ofString "j") .one (localVar "i") (.seq loop afterLoop))
def headerActions : List Action :=
  [.declare "klen" (Find.tableLoad 0#64), .declare "stride" (Find.tableLoad 8#64),
   .declare "keys" (Find.tableLoad 32#64), .declare "vals" (Find.tableLoad 40#64),
   .declare "used" (Find.tableLoad 48#64), .declare "order" (Find.tableLoad 56#64), .declare "order_pos" (Find.tableLoad 64#64)]
def afterIndex : ProgHOL 64 := .dec (ofString "cap") .one (Find.tableLoad 16#64)
  (.seq (.ite (.cmp .equal (localVar "i") (localVar "cap")) returnZero .skip) (program headerActions afterHeaders))

theorem body_shape : body = .decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex := by
  simp only [body, Guest.guestFn_htab_del, progToHOL, expToHOL, shapeToHOL, afterIndex, program, headerActions,
    afterHeaders, afterLoop, lastTest, lastBranch, countStore, returnOne, returnZero, clearUsed, loop, loopBody,
    hashCall, afterHash, moveBranch, moveIndex, positionStore, orderStore, valueStore, copyCall, decision, setMovable,
    beforeHome, afterHome, truth, emptyTest, usedLoad, incrementJ, nextJ, Find.mask, positionRead, wordAddress,
    keyAddress, scaled, Find.tableLoad, localVar, List.map_cons, List.map_nil, Option.map_none]

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.body_shape
