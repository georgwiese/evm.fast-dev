import InitECandidate.Solver.MutableTable.Probe
import InitECandidate.Solver.GasBudget.Frame

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64:=match Guest.guestFn_htab_find_slot with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "t",.one),(ofString "key",.one)]
def tableLoad (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar "t",.const offset])
def usedLoad : ExpHOL 64:=.loadByte (.op .add [localVar "used",localVar "i"])
def condition : ExpHOL 64:=.cmp .notEqual usedLoad (.const 0#64)
def mask : ExpHOL 64:=.op .sub [localVar "cap",.const 1#64]
def initialIndex : ExpHOL 64:=.op .and [localVar "h",mask]
def nextIndex : ExpHOL 64:=.op .and [.op .add [localVar "i",.const 1#64],mask]
def keyAddress : ExpHOL 64:=.op .add [localVar "keys",.panop .mul [localVar "i",localVar "stride"]]
def comparisonArguments : List (ExpHOL 64):=[keyAddress,localVar "key",localVar "klen"]
def equalTest : ExpHOL 64:=.cmp .notEqual (localVar "eq") (.const 0#64)
def afterEqual : ProgHOL 64:=.seq (.ite equalTest (.return (localVar "i")) .skip)
  (.assign .local (ofString "i") nextIndex)
def loopBody : ProgHOL 64:=.decCall (ofString "eq") .one (ofString "memeq") comparisonArguments afterEqual
def loop : ProgHOL 64:=.while condition loopBody
def afterIndex : ProgHOL 64:=.seq loop (.return (localVar "cap"))
def afterHash : ProgHOL 64:=.dec (ofString "i") .one initialIndex afterIndex

theorem body_shape : body=
    .dec (ofString "cap") .one (tableLoad 16#64)
      (.dec (ofString "klen") .one (tableLoad 0#64)
        (.dec (ofString "stride") .one (tableLoad 8#64)
          (.dec (ofString "keys") .one (tableLoad 32#64)
            (.dec (ofString "used") .one (tableLoad 48#64)
              (.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key",localVar "klen"] afterHash))))) := by
  simp only [body,Guest.guestFn_htab_find_slot,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    afterHash,afterIndex,loop,loopBody,condition,usedLoad,afterEqual,equalTest,comparisonArguments,keyAddress,nextIndex,
    initialIndex,mask,tableLoad,localVar]

structure Parameters where
  capacity : BitVec 64
  keyLength : BitVec 64
  stride : BitVec 64
  keys : BitVec 64
  used : BitVec 64
  key : BitVec 64

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64) : Prop where
  cap : source.locals.lookup (ofString "cap")=some (.val (.word p.capacity))
  klen : source.locals.lookup (ofString "klen")=some (.val (.word p.keyLength))
  stride : source.locals.lookup (ofString "stride")=some (.val (.word p.stride))
  keys : source.locals.lookup (ofString "keys")=some (.val (.word p.keys))
  used : source.locals.lookup (ofString "used")=some (.val (.word p.used))
  key : source.locals.lookup (ofString "key")=some (.val (.word p.key))
  index : source.locals.lookup (ofString "i")=some (.val (.word index))

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) (byte : UInt8)
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (p.used+index)=some byte) :
    eval source condition=some (.val (.word (if byte.toNat=0 then 0#64 else 1#64))) := by
  classical
  have notZero : BitVec.ofNat 64 byte.toNat≠0#64 ↔ byte.toNat≠0 := by
    rw [ne_eq,ne_eq]
    have small : byte.toNat<2^64:=by have h : byte.toNat<256:=byte.toNat_lt_size;omega
    have number : (BitVec.ofNat 64 byte.toNat).toNat=byte.toNat := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    apply not_congr
    constructor
    · intro h
      have equal:=congrArg BitVec.toNat h
      rw [number] at equal
      exact equal
    · intro h
      rw [h]
  simp [eval,condition,usedLoad,evalHOLExact,evalListHOLExact,toExact,localVar,locals.used,locals.index,
    valueIsWord,valueWord,wordOpHOL,wordOp,loaded,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,notZero]

theorem next_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) :
    eval source nextIndex=some (.val (.word ((index+1#64) &&& (p.capacity-1#64)))) := by
  have fold : ∀ x y : BitVec 64,AndOp.and x (AndOp.and y (18446744073709551615#64))=x &&& y := by
    intro x y
    change x &&& (y &&& BitVec.allOnes 64)=x &&& y
    rw [BitVec.and_allOnes]
  simp [eval,nextIndex,mask,evalHOLExact,evalListHOLExact,toExact,localVar,locals.cap,locals.index,
    valueIsWord,valueWord,wordOpHOL,wordOp,fold]

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.body_shape
#print axioms InitECandidate.Solver.MutableTable.Find.condition_read
#print axioms InitECandidate.Solver.MutableTable.Find.next_read
