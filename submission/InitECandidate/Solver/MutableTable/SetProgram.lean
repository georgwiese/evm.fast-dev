import InitECandidate.Solver.MutableTable.InsertProgram
import InitECandidate.Solver.MutableTable.GetTail32

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_htab_set with | .function fn=>progToHOL fn.body | _=>.skip
def presentTest : ExpHOL 64:=.cmp .notEqual (localVar "i") (Find.tableLoad 16#64)
def updateBranch : ProgHOL 64:=.seq Insert.valueStore Insert.returnZero
def growthExpression : ExpHOL 64:=.panop .mul [.op .add [Find.tableLoad 24#64,.const 1#64],.const 2#64]
def growthTest : ExpHOL 64:=.cmp .lower (Find.tableLoad 16#64) growthExpression
def growCall : ProgHOL 64:=.call (some (none,none)) (ofString "htab_grow") [localVar "t"]
def insertCall : ProgHOL 64:=.call (some (none,none)) (ofString "htab_insert_raw")
  [localVar "t",localVar "key",localVar "value"]
def afterPresent : ProgHOL 64:=.seq (.ite growthTest growCall .skip) (.seq insertCall Insert.returnZero)
def afterIndex : ProgHOL 64:=.seq (.ite presentTest updateBranch .skip) afterPresent

theorem body_shape : body=.decCall (ofString "i") .one (ofString "htab_find_slot")
    [localVar "t",localVar "key"] afterIndex := by
  simp only [body,Guest.guestFn_htab_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterIndex,afterPresent,presentTest,updateBranch,growthTest,growthExpression,growCall,insertCall,
    Insert.valueStore,Insert.scaled,Insert.returnZero,Find.tableLoad,localVar,Option.map_none]

/-- The actual growth guard is false throughout an immutable build whose
capacity was selected to leave room for twice the full record count. -/
theorem no_growth (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tableAddress : BitVec 64)
    (count capacity records : Nat) (countBound : count≤records) (room : 2*records+2≤capacity)
    (capacitySmall : capacity<2^64)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word tableAddress)))
    (mapped : ∀ offset∈([16,24] : List Nat),source.memaddrs (tableAddress+BitVec.ofNat 64 offset))
    (capCell : source.memory (tableAddress+16#64)=.word (BitVec.ofNat 64 capacity))
    (countCell : source.memory (tableAddress+24#64)=.word (BitVec.ofNat 64 count)) :
    evaluateHOLFiniteState source (.ite growthTest growCall .skip)=(none,source) := by
  have capRead:=Find.table_read source tableAddress 16#64 (BitVec.ofNat 64 capacity) tLocal
    (mapped 16 (by simp)) capCell
  have countRead:=Find.table_read source tableAddress 24#64 (BitVec.ofNat 64 count) tLocal
    (mapped 24 (by simp)) countCell
  have countSmall : count+1<2^64:=by omega
  have twiceSmall : (count+1)*2<2^64:=by omega
  have sum : BitVec.ofNat 64 count+1#64=BitVec.ofNat 64 (count+1):=by rw [BitVec.ofNat_add]
  have product : BitVec.ofNat 64 (count+1)*2#64=BitVec.ofNat 64 ((count+1)*2):=by rw [BitVec.ofNat_mul]
  have comparison : ¬ (BitVec.ofNat 64 ((count+1)*2)).toNat>(BitVec.ofNat 64 capacity).toNat := by
    rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt twiceSmall,Nat.mod_eq_of_lt capacitySmall]
    omega
  simp only [eval] at capRead countRead
  have numeric : ¬ capacity<(count+1)*2:=by omega
  simp [evaluateHOLFiniteState_ite,growthTest,growthExpression,evalHOLExact,evalListHOLExact,toExact,
    capRead,countRead,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,sum,product,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,comparison,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt twiceSmall,Nat.mod_eq_of_lt capacitySmall,numeric]
  intro impossible
  omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.body_shape
#print axioms InitECandidate.Solver.MutableTable.Set.no_growth
