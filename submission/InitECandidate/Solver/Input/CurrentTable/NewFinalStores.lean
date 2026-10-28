import InitECandidate.Solver.Input.CurrentTable.NewFinalEntry

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def finishStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64) :=
  putField (putField (putField (putField source table 56 0#64) table 64 1#64) table 72 0#64) table 80 cap

set_option maxRecDepth 100000 in
theorem final_fields_shape : finalFields=.seq (.store (Scalar.plus (localVar "t") 56) (.const 0#64))
    (.seq (.store (Scalar.plus (localVar "t") 64) (.const 1#64))
    (.seq (.store (Scalar.plus (localVar "t") 72) (.const 0#64))
    (.seq (.store (Scalar.plus (localVar "t") 80) (localVar "ncap")) (.return (localVar "t"))))) := by
  simp only [keysCall,afterKeys,nodesCall,afterNodes,orderCall,afterOrder,finalFields,
    fields,afterNcap,afterStride,afterTable,body,Guest.Software.guestFn_htab_new,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Scalar.plus,localVar,CallPrefix.cutAt]

/-- The actual final metadata stores install the empty root/free list,
next-node1 and current node capacity, then return this fresh table. -/
theorem final_fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (ncapCell : source.locals.lookup (ofString "ncap")=some (.val (.word cap))) :
    evaluateHOLFiniteState source finalFields=(some (.returned (.val (.word table))),emptyLocalsHOLFinite (finishStored source table cap)) := by
  let first:=putField source table 56 0#64
  let second:=putField first table 64 1#64
  let third:=putField second table 72 0#64
  have one:=store_field source table 0#64 56 (.const 0#64) domain arena aligned (by decide) (by decide) tableCell rfl
  have two:=store_field first table 1#64 64 (.const 1#64) domain arena aligned (by decide) (by decide) tableCell rfl
  have three:=store_field second table 0#64 72 (.const 0#64) domain arena aligned (by decide) (by decide) tableCell rfl
  have four:=store_field third table cap 80 (localVar "ncap") domain arena aligned (by decide) (by decide) tableCell (Request.local_word third "ncap" cap ncapCell)
  rw [final_fields_shape,evaluateHOLFiniteState_seq_line780,one]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,two]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,three]
  simp only
  rw [evaluateHOLFiniteState_seq_line780,four]
  simp only
  change evaluateHOLFiniteState (finishStored source table cap) (.return (localVar "t"))=_
  simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,show (finishStored source table cap).locals.lookup (ofString "t")=some (.val (.word table)) from tableCell,
    shapeOfHOLExact]

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.final_fields_execute
