import InitECandidate.Solver.Mpt.IndexedCounter
import InitECandidate.Solver.Mpt.SetEnvironment
import InitECandidate.Solver.Input.VarList.Layout
import InitECandidate.Solver.Mpt.TrieWalkValues

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.VarList

/-- Actual input rows retained below the indexed builder's allocation
frontier. Empty arrays require no allocation or readable null pointer. -/
structure SliceArray (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop) : Prop where
  allocation : count≠0→AllocatedBytes.Arena array (16*count)
  aligned : count≠0→array.toNat%8=0
  above : count≠0→2713731432≤array.toNat
  before : count≠0→array.toNat+16*count≤cutoff
  cells : ∀ index<count,source.memory (row array index)=.word (slices index).1 ∧
    source.memory (lengthCell array index)=.word (slices index).2
  payload : ∀ index<count,TrieWalk.Payload source.memaddrs (slices index).1 (slices index).2 limit
  extra : ∀ index<count,property (slices index).1 (slices index).2

theorem SliceArray.row_numbers (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (data : SliceArray source array count cutoff limit slices property) (index : Nat) (inside : index<count) :
    (row array index).toNat=array.toNat+16*index ∧ (lengthCell array index).toNat=array.toNat+16*index+8 := by
  have active : count≠0:=by omega
  have upper:=(data.allocation active).upper
  have first : (row array index).toNat=array.toNat+16*index:=byteAddress_toNat array (16*index) (by omega)
  exact ⟨first,by rw [lengthCell,BitVec.toNat_add_of_lt (by change (row array index).toNat+8<2^64; rw [first]; omega),first]; rfl⟩

/-- Agreement on the real older array band retains all actual rows and
payload ownership after either key scratch writes or a trie update. -/
theorem SliceArray.of_band (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (data : SliceArray source array count cutoff limit slices property) (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<cutoff→target.memory query=source.memory query) :
    SliceArray target array count cutoff limit slices property := by
  refine ⟨data.allocation,data.aligned,data.above,data.before,?_,?_,data.extra⟩
  · intro index inside
    have active : count≠0:=by omega
    have numbers:=data.row_numbers source array count cutoff limit slices property index inside
    have lower:=data.above active
    have upper:=data.before active
    exact ⟨(memory _ (by rw [numbers.1]; omega) (by rw [numbers.1]; omega)).trans (data.cells index inside).1,
      (memory _ (by rw [numbers.2]; omega) (by rw [numbers.2]; omega)).trans (data.cells index inside).2⟩
  · intro index inside
    rw [domain]
    exact data.payload index inside

/-- The literal indexed setter arguments read the selected original row,
using its true current counter and the encoder's actual returned length. -/
theorem set_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array m index : BitVec 64)
    (count cutoff limit encoded : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (data : SliceArray source array count cutoff limit slices property) (inside : index.toNat<count)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array)))
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))))
    (keyCell : source.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word 2713717624#64))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) setArguments=
      some (SetTrie.values m 2713717624#64 (BitVec.ofNat 64 encoded) (slices index.toNat).1 (slices index.toNat).2) := by
  have active : count≠0:=by omega
  have mapped:=AllocatedBytes.word_mapped source array (16*count) (16*index.toNat) domain (data.allocation active) (by omega) (data.aligned active) (by omega)
  have lengthMapped:=AllocatedBytes.word_mapped source array (16*count) (16*index.toNat+8) domain (data.allocation active) (by omega) (data.aligned active) (by omega)
  have cells:=data.cells index.toNat inside
  have product : BitVec.ofNat 64 (16*index.toNat)=index*16#64:=by simp [BitVec.ofNat_mul,BitVec.mul_comm]
  simp only [row,Input.VarList.lengthCell,byteAddress,BitVec.ofNat_add,product,BitVec.add_assoc] at cells mapped lengthMapped
  simp [setArguments,SetTrie.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,arrayCell,mCell,indexCell,lengthCell,keyCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,BitVec.add_assoc,mapped,lengthMapped,cells.1,cells.2]

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.SliceArray.row_numbers
#print axioms InitECandidate.Solver.Mpt.Indexed.SliceArray.of_band
#print axioms InitECandidate.Solver.Mpt.Indexed.set_arguments
