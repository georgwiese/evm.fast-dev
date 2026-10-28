import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Initialized

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Real physical builder input before its capacity/constructor prefix.
The future table/cap fields of Data are unused at this boundary. -/
structure Entry (data : Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  workspace : Workspace source data.upper data.stp data.pad
  little : source.be=false
  rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper
  outCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out))
  arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word data.array))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.total)))
  totalSmall : data.total<2^31
  stateBefore : data.stp.toNat+200≤data.lower
  padBefore : data.pad.toNat+136≤data.lower
  outBefore : data.out.toNat+32≤data.lower
  outArena : AllocatedBytes.Arena data.out 32
  outAligned : data.out.toNat%8=0
  lowerUpper : data.lower≤data.upper
  lowerSmall : data.lower<2^64
  lengths : ∀ index<data.total,(data.lengths index).toNat≤data.itemLimit
  itemSmall : data.itemLimit+136<2^64

theorem Entry.at_table {data : Data} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Entry data source) (table cap : BitVec 64) (capacity : 2*data.total+2≤cap.toNat) (before : data.upper≤table.toNat) :
    Layout {data with table:=table,cap:=cap} :=
  ⟨entry.totalSmall,capacity,before,entry.stateBefore,entry.padBefore,entry.outBefore,entry.outArena,entry.outAligned,
    entry.lowerUpper,entry.lowerSmall,entry.lengths,entry.itemSmall⟩

theorem Entry.of_frame {data : Data} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Entry data source) (frame : LocalEffects.erase target=LocalEffects.erase source)
    (arrayCell : target.locals.lookup (ofString "slice_arr")=some (.val (.word data.array)))
    (countCell : target.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.total)))) : Entry data target := by
  have endian := congrArg PanSemStateFiniteExact.be frame
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change target.be=source.be at endian
  change target.globals=source.globals at globals
  have memory := LocalEffects.memory_of_erase source target frame
  exact ⟨entry.workspace.of_frame frame,endian.trans entry.little,
    entry.rows.of_frame source target data.array data.pointers data.lengths data.total data.lower data.upper ⟨by intro query lower upper; exact congrFun memory query⟩,
    (by rw [globals]; exact entry.outCell),arrayCell,countCell,entry.totalSmall,entry.stateBefore,entry.padBefore,entry.outBefore,
    entry.outArena,entry.outAligned,entry.lowerUpper,entry.lowerSmall,entry.lengths,entry.itemSmall⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.Entry.at_table
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.Entry.of_frame
