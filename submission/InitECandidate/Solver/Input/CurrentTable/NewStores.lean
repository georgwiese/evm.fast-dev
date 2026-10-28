import InitECandidate.Solver.Input.CurrentTable.NewProgram
import InitECandidate.Solver.Input.CallPrefix
import InitECandidate.Solver.Input.ScalarProgram
import InitECandidate.Solver.Input.LocalWord
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def keysCall : ProgHOL 64 := (CallPrefix.cutAt 4 fields).2

def putField (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (offset : Nat) (value : BitVec 64) :=
  {source with memory:=StoreWord.put source.memory (table+BitVec.ofNat 64 offset) value}

def headerStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64) :=
  putField (putField (putField (putField source table 0 32#64) table 8 32#64) table 16 cap) table 24 0#64

set_option maxRecDepth 100000 in
theorem fields_shape : fields=.seq (.store (Scalar.plus (localVar "t") 0) (localVar "key_len"))
    (.seq (.store (Scalar.plus (localVar "t") 8) (localVar "stride"))
    (.seq (.store (Scalar.plus (localVar "t") 16) (localVar "cap"))
    (.seq (.store (Scalar.plus (localVar "t") 24) (.const 0#64)) keysCall))) := by
  simp only [keysCall,fields,afterNcap,afterStride,afterTable,body,Guest.Software.guestFn_htab_new,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Scalar.plus,localVar,CallPrefix.cutAt]

theorem store_field (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (offset : Nat) (expression : ExpHOL 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88)
    (aligned : table.toNat%8=0) (inside : offset<88) (offsetAligned : offset%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (read : eval source expression=some (.val (.word value))) :
    evaluateHOLFiniteState source (.store (Scalar.plus (localVar "t") offset) expression)=(none,putField source table offset value) := by
  exact StoreWord.execute source _ _ _ _
    (Scalar.plus_read source (localVar "t") table offset (Request.local_word source "t" table tableCell)) read
    (AllocatedBytes.word_mapped source table 88 offset domain arena inside aligned offsetAligned)

/-- Derived room for the real88-byte allocation makes all four initial
metadata stores execute. This includes cap at16 and the actual empty count
at24; the next current array-allocation caller remains unchanged. -/
theorem fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key_len")=some (.val (.word 32#64)))
    (strideCell : source.locals.lookup (ofString "stride")=some (.val (.word 32#64)))
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word cap))) :
    evaluateHOLFiniteState source fields=evaluateHOLFiniteState (headerStored source table cap) keysCall := by
  let first:=putField source table 0 32#64
  let second:=putField first table 8 32#64
  let third:=putField second table 16 cap
  have one:=store_field source table 32#64 0 (localVar "key_len") domain arena aligned (by decide) (by decide) tableCell (Request.local_word source "key_len" 32#64 keyCell)
  have two:=store_field first table 32#64 8 (localVar "stride") domain arena aligned (by decide) (by decide) tableCell (Request.local_word first "stride" 32#64 strideCell)
  have three:=store_field second table cap 16 (localVar "cap") domain arena aligned (by decide) (by decide) tableCell (Request.local_word second "cap" cap capCell)
  have four:=store_field third table 0#64 24 (.const 0#64) domain arena aligned (by decide) (by decide) tableCell rfl
  rw [fields_shape,evaluateHOLFiniteState_seq_line780,one]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,two]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,three]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,four]
  rfl

/-- Initial current metadata stores protect every earlier input word. -/
theorem header_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap query : BitVec 64)
    (arena : AllocatedBytes.Arena table 88) (before : query.toNat<table.toNat) :
    (headerStored source table cap).memory query=source.memory query := by
  have away (offset : Nat) (inside : offset<88) : query≠table+BitVec.ofNat 64 offset := by
    have number:=byteAddress_toNat table offset (by have bound:=arena.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
    intro same
    have equal:=congrArg BitVec.toNat same
    rw [number] at equal
    omega
  have zeroAway : query≠table := by intro same; subst query; omega
  simp [headerStored,putField,StoreWord.put,zeroAway,away 8 (by decide),away 16 (by decide),away 24 (by decide)]

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.fields_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.New.header_before
