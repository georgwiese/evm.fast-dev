import InitECandidate.Solver.MutableTable.FindDictionaryCall32

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_htab_get with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=Find.formals
def pair (flag value : BitVec 64) : ValueHOL 64:=.rStruct [.val (.word flag),.val (.word value)]
def output : Option (BitVec 64)→ValueHOL 64
  | none=>pair 0#64 0#64
  | some value=>pair 1#64 value

def condition : ExpHOL 64:=.cmp .equal (localVar "i") (Find.tableLoad 16#64)
def valueExpression : ExpHOL 64:=.load .one (.op .add [Find.tableLoad 40#64,.panop .mul [localVar "i",.const 8#64]])
def absent : ProgHOL 64:=.return (.rstruct [.const 0#64,.const 0#64])
def present : ProgHOL 64:=.return (.rstruct [.const 1#64,valueExpression])
def afterIndex : ProgHOL 64:=.seq (.ite condition absent .skip) present

theorem body_shape : body=.decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t",localVar "key"] afterIndex := by
  simp only [body,Guest.guestFn_htab_get,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterIndex,condition,absent,present,valueExpression,Find.tableLoad,localVar]

/-- The literal get suffix performs the actual value-cell read, or the exact
absent return, from find's represented slot specification. No body clocks. -/
theorem tail32_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tableAddress vals index sentinel : BitVec 64)
    (bits : Nat) (small : bits<64) (capNumber : sentinel=BitVec.ofNat 64 (2^bits))
    (table : Find.Model32 (BitVec 64)) (dictionary : Find.Key32→Option (BitVec 64)) (query : Find.Key32)
    (tLocal : source.locals.lookup (ofString "t")=some (.val (.word tableAddress)))
    (iLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (capMapped : source.memaddrs (tableAddress+16#64)) (capCell : source.memory (tableAddress+16#64)=.word sentinel)
    (valsMapped : source.memaddrs (tableAddress+40#64)) (valsCell : source.memory (tableAddress+40#64)=.word vals)
    (values : ∀ i<2^bits,∀ key value,table i=some (key,value)→
      source.memaddrs (vals+BitVec.ofNat 64 i*8#64) ∧ source.memory (vals+BitVec.ofNat 64 i*8#64)=.word value)
    (spec : Find.SlotSpec32 (2^bits) sentinel index table dictionary query) :
    evaluateHOLFiniteState source afterIndex=(some (.returned (output (dictionary query))),emptyLocalsHOLFinite source) := by
  classical
  have capRead:=Find.table_read source tableAddress 16#64 sentinel tLocal capMapped capCell
  simp only [eval] at capRead
  rcases spec with ⟨same,noValue⟩|⟨slot,value,inside,indexNat,stored,dictValue⟩
  · have stopped : evaluateHOLFiniteState source (.ite condition absent .skip)=
        (some (.returned (pair 0#64 0#64)),emptyLocalsHOLFinite source) := by
      simp [condition,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,iLocal,capRead,same,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,absent,pair,evaluateHOLFiniteState_return,evalListHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [afterIndex,WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ stopped (Nat.le_refl _),noValue]
    rfl
  · have capSmall : 2^bits<2^64:=Nat.pow_lt_pow_right (by decide) small
    have slotSmall : slot<2^64:=by omega
    have indexWord : index=BitVec.ofNat 64 slot := by
      apply BitVec.eq_of_toNat_eq
      rw [indexNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt slotSmall]
    have capNat : sentinel.toNat=2^bits := by rw [capNumber,BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
    have different : index≠sentinel := by
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [indexNat,capNat] at numeric
      omega
    have skipped : evaluateHOLFiniteState source (.ite condition absent .skip)=(none,source) := by
      simp [condition,evaluateHOLFiniteState_ite,evalHOLExact,toExact,localVar,iLocal,capRead,different,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have valsRead:=Find.table_read source tableAddress 40#64 vals tLocal valsMapped valsCell
    obtain ⟨valueMapped,valueCell⟩:=values slot inside query value stored
    have read : eval source valueExpression=some (.val (.word value)) := by
      simp only [eval] at valsRead ⊢
      rw [indexWord] at iLocal
      simp [valueExpression,evalHOLExact,evalListHOLExact,toExact,localVar,iLocal,valsRead,valueIsWord,valueWord,wordOpHOL,wordOp,
        panOpHOL,memLoadHOLExact,isWfShapeExactHOL,valueMapped,valueCell]
    have returned : evaluateHOLFiniteState source present=(some (.returned (pair 1#64 value)),emptyLocalsHOLFinite source) := by
      simp only [eval] at read
      simp [present,pair,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,read,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    rw [afterIndex,WitnessRadix.StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _),dictValue]
    exact returned

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.body_shape
#print axioms InitECandidate.Solver.MutableTable.Get.tail32_execute
