import InitECandidate.Solver.MutableTable.HashCall32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def headerActions : List Action:=[.declare "cap" (tableLoad 16#64),.declare "klen" (tableLoad 0#64),
  .declare "stride" (tableLoad 8#64),.declare "keys" (tableLoad 32#64),.declare "used" (tableLoad 48#64)]
def hashCall : ProgHOL 64:=.decCall (ofString "h") .one (ofString "htab_hash") [localVar "key",localVar "klen"] afterHash
def headerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  bind (bind (bind (bind (bind source "cap" p.capacity) "klen" p.keyLength) "stride" p.stride) "keys" p.keys) "used" p.used

structure HeaderCells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters) : Prop where
  tableLocal : source.locals.lookup (ofString "t")=some (.val (.word table))
  keyLocal : source.locals.lookup (ofString "key")=some (.val (.word p.key))
  mapped : ∀ offset∈([0,8,16,32,48] : List Nat),source.memaddrs (table+BitVec.ofNat 64 offset)
  capacity : source.memory (table+16#64)=.word p.capacity
  keyLength : source.memory table=.word p.keyLength
  stride : source.memory (table+8#64)=.word p.stride
  keys : source.memory (table+32#64)=.word p.keys
  used : source.memory (table+48#64)=.word p.used

theorem header_shape : body=WitnessRadix.ProgramPrefix.program headerActions hashCall := by
  rw [body_shape]
  rfl

theorem table_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table offset word : BitVec 64)
    (t : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (mapped : source.memaddrs (table+offset)) (stored : source.memory (table+offset)=.word word) :
    eval source (tableLoad offset)=some (.val (.word word)) := by
  simp [eval,tableLoad,evalHOLExact,evalListHOLExact,toExact,localVar,t,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

/-- All five actual header declarations, preserving complete memory/control
and retaining their exact lexical restore stack. -/
theorem header_executes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (cells : HeaderCells source table p) :
    ∃ restoreStack,Executes source headerActions (headerState source p) restoreStack := by
  let sc:=bind source "cap" p.capacity
  let sl:=bind sc "klen" p.keyLength
  let ss:=bind sl "stride" p.stride
  let sk:=bind ss "keys" p.keys
  have tC : sc.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "cap" "t" _ (by decide)).trans cells.tableLocal
  have tL : sl.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "klen" "t" _ (by decide)).trans tC
  have tS : ss.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "stride" "t" _ (by decide)).trans tL
  have tK : sk.locals.lookup (ofString "t")=some (.val (.word table)):=
    (bind_lookup_other _ "keys" "t" _ (by decide)).trans tS
  have cap:=table_read source table 16#64 p.capacity cells.tableLocal (cells.mapped 16 (by simp)) cells.capacity
  have len:=table_read sc table 0#64 p.keyLength tC (cells.mapped 0 (by simp))
    (by change source.memory (table+0#64)=.word p.keyLength;simpa using cells.keyLength)
  have stride:=table_read sl table 8#64 p.stride tL (cells.mapped 8 (by simp)) cells.stride
  have keys:=table_read ss table 32#64 p.keys tS (cells.mapped 32 (by simp)) cells.keys
  have used:=table_read sk table 48#64 p.used tK (cells.mapped 48 (by simp)) cells.used
  exact ⟨_,.declare p.capacity cap (.declare p.keyLength len (.declare p.stride stride
    (.declare p.keys keys (.declare p.used used (.done _)))))⟩

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.header_shape
#print axioms InitECandidate.Solver.MutableTable.Find.table_read
#print axioms InitECandidate.Solver.MutableTable.Find.header_executes
