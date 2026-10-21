import InitECandidate.Solver.Mpt.WitnessDecodeRowReads
import InitECandidate.Solver.Rlp.SliceRecordsFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current physical slice-array cells and the original pure input-range
facts. Later parsing uses its actual current bytes; runtime accounting needs
only these real row words and bounded intervals. -/
structure Rows (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  records : Rlp.Slices.Records source.memory array pointer items
  allocation : AllocatedBytes.Arena array (16*items.length)
  aligned : array.toNat%8=0
  fits : pointer.toNat+bytes<2^64
  intervals : ∀ index item,items[index]?=some item→
    1≤item.total.toNat ∧ item.total.toNat≤bytes ∧
    pointer.toNat≤(Rlp.Slices.itemPointer pointer items index).toNat ∧
    (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat≤pointer.toNat+bytes

theorem Rows.of_model (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (domain : source.memaddrs=InitE.ordinaryDomain) (model : Rlp.ListItems source pointer bytes items)
    (records : Rlp.Slices.Records source.memory array pointer items)
    (allocation : AllocatedBytes.Arena array (16*items.length)) (aligned : array.toNat%8=0)
    (fits : pointer.toNat+bytes<2^64) : Rows source array pointer bytes items := by
  refine ⟨domain,records,allocation,aligned,fits,?_⟩
  intro index item selected
  obtain ⟨offset,location,extent,valid,encoded⟩:=model.at source pointer bytes items index item selected
  have span:=model.at_span source pointer bytes items index item selected fits
  have offsetNumber : (BitVec.ofNat 64 offset).toNat=offset:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have pointerNumber : (Rlp.Slices.itemPointer pointer items index).toNat=pointer.toNat+offset:=by
    rw [location,BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega),offsetNumber]
  exact ⟨span.2.1,span.2.2.1,by rw [pointerNumber]; omega,by rw [pointerNumber,span.1]; omega⟩

/-- Transport rows through agreement only on their own physical array.
Their original pure size/interval bounds survive unrelated memory changes. -/
theorem Rows.frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (rows : Rows source array pointer bytes items)
    (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,array.toNat≤query.toNat→query.toNat<array.toNat+16*items.length→target.memory query=source.memory query) :
    Rows target array pointer bytes items :=
  ⟨domain.trans rows.domain,Rlp.Slices.Records.of_interval source target array pointer items rows.records
    (by have upper:=rows.allocation.upper; omega) memory,rows.allocation,rows.aligned,rows.fits,rows.intervals⟩

theorem Rows.above (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (rows : Rows source array pointer bytes items)
    (cursor : Nat) (below : cursor≤array.toNat) (domain : target.memaddrs=source.memaddrs)
    (memory : Rlp.Validation.Above source target cursor) : Rows target array pointer bytes items :=
  rows.frame source target array pointer bytes items domain (fun query lower upper=>memory query (below.trans lower))

theorem Rows.earlier (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (rows : Rows source array pointer bytes items)
    (frontier : Nat) (before : array.toNat+16*items.length≤frontier) (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,query.toNat<frontier→target.memory query=source.memory query) : Rows target array pointer bytes items :=
  rows.frame source target array pointer bytes items domain (fun query lower upper=>memory query (upper.trans_le before))

/-- Current row cells alone supply both real argument words and all input
range bounds required for an actual original path/value item call. -/
theorem Rows.arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (rows : Rows source array pointer bytes items)
    (item : Rlp.ListItem) (selected : items[index]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (recordArguments index)=
      some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items index) item.total) ∧
      1≤item.total.toNat ∧ item.total.toNat≤bytes ∧
      pointer.toNat≤(Rlp.Slices.itemPointer pointer items index).toNat ∧
      (Rlp.Slices.itemPointer pointer items index).toNat+item.total.toNat≤pointer.toNat+bytes :=
  ⟨literal_arguments_read source array pointer index items item selected rows.records rows.domain rows.allocation rows.aligned arrayCell,rows.intervals index item selected⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.Rows.of_model
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.Rows.frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.Rows.above
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.Rows.earlier
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.Rows.arguments
